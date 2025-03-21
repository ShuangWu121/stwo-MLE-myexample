use std::iter::zip;

use num_traits::{One, Zero};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, PointEvaluator, TraceLocationAllocator,
};
use crate::core::air::accumulation::PointEvaluationAccumulator;
use crate::core::air::{Component, ComponentProver, Components};
use crate::core::backend::simd::column::BaseColumn;
use crate::core::backend::simd::m31::LOG_N_LANES;
use crate::core::backend::simd::SimdBackend;
use crate::core::channel::{Blake2sChannel, Channel};
use crate::core::circle::CirclePoint;
use crate::core::fields::m31::BaseField;
use crate::core::fields::qm31::SecureField;
use crate::core::lookups::gkr_prover::{prove_batch, Layer};
use crate::core::lookups::mle::Mle;
use crate::core::lookups::utils::Fraction;
use crate::core::pcs::{CommitmentSchemeProver, CommitmentSchemeVerifier, PcsConfig, TreeVec};
use crate::core::poly::circle::{CanonicCoset, CircleEvaluation, PolyOps};
use crate::core::poly::BitReversedOrder;
use crate::core::prover::{prove, verify, StarkProof};
use crate::core::vcs::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use crate::core::ColumnVec;
use crate::examples::xor::gkr_lookups::mle_eval::{
    build_trace, MleCoeffColumnOracle, MleEvalProverComponent,
};
use crate::core::lookups::gkr_verifier::GkrArtifact;
use crate::core::lookups::gkr_verifier::partially_verify_batch;
use crate::core::lookups::gkr_verifier::Gate;


pub type LookupGKRComponent = FrameworkComponent<LookupGKREval>;

const MLE_EVAL_TRACE: usize = 2;

#[derive(Clone)]
pub struct LookupGKREval {
    // the length of the trace
    pub log_n_rows: u32,
}
impl FrameworkEval for LookupGKREval {
    fn log_size(&self) -> u32 {
        self.log_n_rows
    }
    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_n_rows + 2
    }
    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let _a = eval.next_trace_mask();
        let _b = eval.next_trace_mask();

        eval
    }
}

impl MleCoeffColumnOracle for LookupGKRComponent {
    fn evaluate_at_point(
        &self,
        _point: CirclePoint<SecureField>,
        mask: &TreeVec<ColumnVec<Vec<SecureField>>>,
    ) -> SecureField {
        println!("evaluate_at_point for MLE");

        println!(
            "\n the point evaluator mask is {:?}",
            mask.sub_tree(self.trace_locations())
        );
        // Create dummy point evaluator just to extract the value we need from the mask
        let mut accumulator = PointEvaluationAccumulator::new(SecureField::one());
        let mut eval = PointEvaluator::new(
            mask.sub_tree(self.trace_locations()),
            &mut accumulator,
            SecureField::one(),
            self.log_size(),
            SecureField::zero(),
        );

        println!("point evaluator created");

        eval_mle_coeff_col(1, &mut eval)
    }
}

fn eval_mle_coeff_col<E: EvalAtRow>(interaction: usize, eval: &mut E) -> E::EF {
    println!("eval_mle_coeff_col");
    println!("interaction is {:?}", interaction);
    let [mle_coeff_col_eval] = eval.next_interaction_mask(interaction, [0]);
    E::EF::from(mle_coeff_col_eval)
}

#[derive(Clone)]
pub struct LookupGKRCircuitTrace {
    pub a: BaseColumn,
    pub b: BaseColumn,
}
pub fn gen_trace(
    log_size: u32,
    circuit: &LookupGKRCircuitTrace,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_size).circle_domain();
    [&circuit.a, &circuit.b]
        .into_iter()
        .map(|eval| CircleEvaluation::new(domain, eval.clone()))
        .collect()
}

// prove a simple lookup GKR example
// a = [1, 1, 1, ..., 1]
// b = [1, 1, 1, ..., 1]
#[allow(unused)]
pub fn prove_lookup_gkr(
    log_n_rows: u32,
    config: PcsConfig,
) -> (LookupGKRComponent, StarkProof<Blake2sMerkleHasher>) {
    assert!(log_n_rows >= LOG_N_LANES);

    // trace has log_n_rows rows, then the MLE has log_n_rows variables.
    // The MLE has 2^log_n_rows evaluations on boolean hypercube, which are the committed trace
    // values.

    let range = 0..(1 << log_n_rows);

    let mut a: Vec<_> = range.clone().map(|i| 1.into()).collect();
    let mut b: Vec<_> = range.clone().map(|i| 1.into()).collect();

    println!("a is {:?}", a); // a = [0, 1, 2, ..., n]
    println!("b is {:?}", b); // b = [1, 2, ..., 0]
                              // Reorder `a` and `b` before assigning them to the struct
    crate::core::utils::bit_reverse_coset_to_circle_domain_order(&mut a);
    crate::core::utils::bit_reverse_coset_to_circle_domain_order(&mut b);

    // create a and b as basecolumn
    let mut circuit = LookupGKRCircuitTrace {
        a: a.iter().map(|&i: &i32| i.into()).collect(),
        b: b.iter().map(|&i: &i32| i.into()).collect(),
    };
    println!("\n trace a is {:?}", circuit.a);
    println!("trace b is {:?}", circuit.b);

    // Precompute twiddles
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_n_rows + config.fri_config.log_blowup_factor + 2)
            .circle_domain()
            .half_coset,
    );

    // Setup protocol.
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme =
        CommitmentSchemeProver::<_, Blake2sMerkleChannel>::new(config, &twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    let constants_trace_location = tree_builder.extend_evals([]);
    tree_builder.commit(channel);

    // Original Trace.
    let trace = gen_trace(log_n_rows, &circuit);
    let mut tree_builder = commitment_scheme.tree_builder();
    let base_trace_location = tree_builder.extend_evals(trace);
    tree_builder.commit(channel);

    // get random value for logup challenge
    let alpha = channel.draw_felt();

    // create numerator and denominator MLE
    // numerators are all 1
    // denominator a is a-\alpha and denominator b is b-\alpha
    let numerator_values_a: Vec<_> = (0..1 << log_n_rows)
        .map(|_| {
            let a_secure_field = SecureField::from_m31(1.into(), 0.into(), 0.into(), 0.into());
            a_secure_field
        })
        .collect();

    let numerator_values_b: Vec<_> = (0..1 << log_n_rows)
        .map(|_| {
            let b_secure_field = SecureField::from_m31(1.into(), 0.into(), 0.into(), 0.into());
            b_secure_field
        })
        .collect();

    let denominator_values_a: Vec<_> = a
        .iter()
        .map(|&i: &i32| {
            let a_secure_field = SecureField::from_m31(i.into(), 0.into(), 0.into(), 0.into());
            a_secure_field - alpha
        })
        .collect();
    let denominator_values_b: Vec<_> = b
        .iter()
        .map(|&i: &i32| {
            let b_secure_field = SecureField::from_m31(i.into(), 0.into(), 0.into(), 0.into());
            -b_secure_field - alpha
        })
        .collect();

    let sum_a = zip(&numerator_values_a, &denominator_values_a)
        .map(|(&n, &d)| {
            let fraction = Fraction::new(n, d);
            fraction
        })
        .sum::<Fraction<SecureField, SecureField>>();

    let sum_b = zip(&numerator_values_a, &denominator_values_a)
        .map(|(&n, &d)| {
            let fraction = Fraction::new(n, d);
            fraction
        })
        .sum::<Fraction<SecureField, SecureField>>();

    println!("sum a is {:?} \n sum b is {:?}", sum_a, sum_b);

    let numerator_secure_column = numerator_values_a.iter().map(|&i| i).collect();
    let denominator_secure_column = denominator_values_a.iter().map(|&i| i).collect();

    // create multilinear polynomial for the input layer
    let mle_a_numerator = Mle::<SimdBackend, SecureField>::new(numerator_secure_column);
    let mle_a_denominator = Mle::<SimdBackend, SecureField>::new(denominator_secure_column);

    let top_layer = Layer::LogUpGeneric {
        numerators: mle_a_numerator.clone(),
        denominators: mle_a_denominator.clone(),
    };
    let (proof, _) = prove_batch(&mut Blake2sChannel::default(), vec![top_layer]);

    println!("gkr proof generated");

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: _,
    } = partially_verify_batch(vec![Gate::LogUp], &proof, &mut Blake2sChannel::default()).unwrap();

    println!("ood_point is {:?}", ood_point);
    println!("claims_to_verify_by_instance is {:?}", claims_to_verify_by_instance);

    // get evaluation points, mle_a and mle_b should be evaluated at the same points and then
    // combined with linear randomness
    let mut rng = SmallRng::seed_from_u64(0);
    let eval_point: Vec<SecureField> = (0..log_n_rows).map(|_| rng.gen()).collect();

    // get the evaluations of mle_a and mle_b at eval_point
    let claim_a = mle_a_numerator.eval_at_point(&ood_point);
    // let claim_b = mle_b.eval_at_point(&eval_point);

    // Traces for GKR
    // (eq evals + prefix sum).
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(build_trace(&mle_a_numerator, &eval_point, claims_to_verify_by_instance[0][0]));
    tree_builder.commit(channel);

    let trace_location_allocator = &mut TraceLocationAllocator::default();

    // create component for STARK traces
    let component = LookupGKRComponent::new(
        trace_location_allocator,
        LookupGKREval { log_n_rows },
        SecureField::zero(),
    );

    println!("\n component for normal trace is created");

    // create component for MLE
    let mle_eval_component = MleEvalProverComponent::generate(
        trace_location_allocator,
        &component,
        &eval_point,
        mle_a_numerator,
        claim_a,
        &twiddles,
        MLE_EVAL_TRACE,
    );

    println!("\n component for MLE trace is created");

    let components: &[&dyn ComponentProver<SimdBackend>] = &[&component, &mle_eval_component];

    let proof = prove(components, channel, commitment_scheme).unwrap();

    // Verify.
    // TODO: Create Air instance independently.

    // Verify.
    let components = Components {
        components: components.iter().map(|&c| c as &dyn Component).collect(),
        n_preprocessed_columns: 0,
    };

    let log_sizes = components.column_log_sizes();
    let channel = &mut Blake2sChannel::default();

    let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
    commitment_scheme.commit(proof.commitments[0], &[], channel);
    commitment_scheme.commit(proof.commitments[1], &log_sizes[1], channel);
    commitment_scheme.commit(proof.commitments[2], &log_sizes[2], channel);
    verify(
        &components.components,
        channel,
        commitment_scheme,
        proof.clone(),
    );

    println!("pass verification");
    (component, proof)
}

#[cfg(test)]
mod tests {
    use std::env;
    use crate::core::fri::FriConfig;
    use crate::core::pcs::PcsConfig;
    use crate::examples::lookup_gkr::prove_lookup_gkr;

    #[test]
    fn test_simd_lookup_gkr_prove() {
        // Get from environment variable:
        let log_n_instances = env::var("LOG_N_INSTANCES")
            .unwrap_or_else(|_| "5".to_string())
            .parse::<u32>()
            .unwrap();
        let config = PcsConfig {
            pow_bits: 10,
            fri_config: FriConfig::new(0, 1, 100),
        };
        println!(
            "starting test_simd_plonk_prove with log_n_instances: {}",
            log_n_instances
        );

        // Prove.
        prove_lookup_gkr(log_n_instances, config);

        println!("proof is generated ");
    }
}
