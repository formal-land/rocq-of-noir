use acir::{
    circuit::opcodes::{BlackBoxFuncCall, ConstantOrWitnessEnum, FunctionInput},
    native_types::{Witness, WitnessMap},
    AcirField,
};
use acvm_blackbox_solver::{blake2s, blake3, keccakf1600};

use self::{
    aes128::solve_aes128_encryption_opcode, bigint::AcvmBigIntSolver,
    hash::solve_poseidon2_permutation_opcode,
};

use super::{insert_value, OpcodeNotSolvable, OpcodeResolutionError};
use crate::{pwg::input_to_value, BlackBoxFunctionSolver};

mod aes128;
pub(crate) mod bigint;
mod embedded_curve_ops;
mod hash;
mod logic;
mod range;
mod signature;
pub(crate) mod utils;

use embedded_curve_ops::{embedded_curve_add, multi_scalar_mul};
// Hash functions should eventually be exposed for external consumers.
use hash::{solve_generic_256_hash_opcode, solve_sha_256_permutation_opcode};
use logic::{and, xor};
pub(crate) use range::solve_range_opcode;
use signature::ecdsa::{secp256k1_prehashed, secp256r1_prehashed};

/// Check if all of the inputs to the function have assignments
///
/// Returns the first missing assignment if any are missing
fn first_missing_assignment<F>(
    witness_assignments: &WitnessMap<F>,
    inputs: &[FunctionInput<F>],
) -> Option<Witness> {
    inputs.iter().find_map(|input| {
        if let ConstantOrWitnessEnum::Witness(ref witness) = input.input_ref() {
            if witness_assignments.contains_key(witness) {
                None
            } else {
                Some(*witness)
            }
        } else {
            None
        }
    })
}

/// Check if all of the inputs to the function have assignments
fn contains_all_inputs<F>(
    witness_assignments: &WitnessMap<F>,
    inputs: &[FunctionInput<F>],
) -> bool {
    first_missing_assignment(witness_assignments, inputs).is_none()
}

pub(crate) fn solve<F: AcirField>(
    backend: &impl BlackBoxFunctionSolver<F>,
    initial_witness: &mut WitnessMap<F>,
    bb_func: &BlackBoxFuncCall<F>,
    bigint_solver: &mut AcvmBigIntSolver,
) -> Result<(), OpcodeResolutionError<F>> {
    let inputs = bb_func.get_inputs_vec();
    if !contains_all_inputs(initial_witness, &inputs) {
        let unassigned_witness = first_missing_assignment(initial_witness, &inputs)
            .expect("Some assignments must be missing because it does not contains all inputs");
        return Err(OpcodeResolutionError::OpcodeNotSolvable(
            OpcodeNotSolvable::MissingAssignment(unassigned_witness.0),
        ));
    }

    match bb_func {
        BlackBoxFuncCall::AES128Encrypt { inputs, iv, key, outputs } => {
            solve_aes128_encryption_opcode(initial_witness, inputs, iv, key, outputs)
        }
        BlackBoxFuncCall::AND { lhs, rhs, output } => {
            and(initial_witness, lhs, rhs, output, backend.pedantic_solving())
        }
        BlackBoxFuncCall::XOR { lhs, rhs, output } => {
            xor(initial_witness, lhs, rhs, output, backend.pedantic_solving())
        }
        BlackBoxFuncCall::RANGE { input } => {
            solve_range_opcode(initial_witness, input, backend.pedantic_solving())
        }
        BlackBoxFuncCall::Blake2s { inputs, outputs } => {
            solve_generic_256_hash_opcode(initial_witness, inputs, None, outputs, blake2s)
        }
        BlackBoxFuncCall::Blake3 { inputs, outputs } => {
            solve_generic_256_hash_opcode(initial_witness, inputs, None, outputs, blake3)
        }
        BlackBoxFuncCall::Keccakf1600 { inputs, outputs } => {
            let mut state = [0; 25];
            for (it, input) in state.iter_mut().zip(inputs.as_ref()) {
                let num_bits = input.num_bits() as usize;
                assert_eq!(num_bits, 64);
                let witness_assignment = input_to_value(initial_witness, *input, false)?;
                let lane = witness_assignment.try_to_u64();
                *it = lane.unwrap();
            }
            let output_state = keccakf1600(state)?;
            for (output_witness, value) in outputs.iter().zip(output_state.into_iter()) {
                insert_value(output_witness, F::from(value as u128), initial_witness)?;
            }
            Ok(())
        }
        BlackBoxFuncCall::EcdsaSecp256k1 {
            public_key_x,
            public_key_y,
            signature,
            hashed_message: message,
            output,
        } => secp256k1_prehashed(
            initial_witness,
            public_key_x,
            public_key_y,
            signature,
            message.as_ref(),
            *output,
        ),
        BlackBoxFuncCall::EcdsaSecp256r1 {
            public_key_x,
            public_key_y,
            signature,
            hashed_message: message,
            output,
        } => secp256r1_prehashed(
            initial_witness,
            public_key_x,
            public_key_y,
            signature,
            message.as_ref(),
            *output,
        ),
        BlackBoxFuncCall::MultiScalarMul { points, scalars, outputs } => {
            multi_scalar_mul(backend, initial_witness, points, scalars, *outputs)
        }
        BlackBoxFuncCall::EmbeddedCurveAdd { input1, input2, outputs } => {
            embedded_curve_add(backend, initial_witness, **input1, **input2, *outputs)
        }
        // Recursive aggregation will be entirely handled by the backend and is not solved by the ACVM
        BlackBoxFuncCall::RecursiveAggregation { .. } => Ok(()),
        BlackBoxFuncCall::BigIntAdd { lhs, rhs, output }
        | BlackBoxFuncCall::BigIntSub { lhs, rhs, output }
        | BlackBoxFuncCall::BigIntMul { lhs, rhs, output }
        | BlackBoxFuncCall::BigIntDiv { lhs, rhs, output } => {
            bigint_solver.bigint_op(*lhs, *rhs, *output, bb_func.get_black_box_func())
        }
        BlackBoxFuncCall::BigIntFromLeBytes { inputs, modulus, output } => {
            bigint_solver.bigint_from_bytes(inputs, modulus, *output, initial_witness)
        }
        BlackBoxFuncCall::BigIntToLeBytes { input, outputs } => {
            bigint_solver.bigint_to_bytes(*input, outputs, initial_witness)
        }
        BlackBoxFuncCall::Sha256Compression { inputs, hash_values, outputs } => {
            solve_sha_256_permutation_opcode(initial_witness, inputs, hash_values, outputs)
        }
        BlackBoxFuncCall::Poseidon2Permutation { inputs, outputs, len } => {
            solve_poseidon2_permutation_opcode(backend, initial_witness, inputs, outputs, *len)
        }
    }
}
