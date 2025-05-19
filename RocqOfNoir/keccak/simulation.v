Require Import RocqOfNoir.RocqOfNoir.
Require Import RocqOfNoir.proof.RocqOfNoir.
Require Import RocqOfNoir.simulation.RocqOfNoir.
Require RocqOfNoir.keccak.polymorphic.

(* global BLOCK_SIZE_IN_BYTES: u32 = 136; *)
Definition BLOCK_SIZE_IN_BYTES: Z := 136.

(* global WORD_SIZE: u32 = 8; *)
Definition WORD_SIZE: Z := 8.

(* global LIMBS_PER_BLOCK: u32 = BLOCK_SIZE_IN_BYTES / WORD_SIZE; *)
Definition LIMBS_PER_BLOCK: Z := BLOCK_SIZE_IN_BYTES / WORD_SIZE.

(* global NUM_KECCAK_LANES: u32 = 25; *)
Definition NUM_KECCAK_LANES: Z := 25.

(*
pub fn keccak256<let N: u32>(input: [u8; N], message_size: u32) -> [u8; 32] {
    assert(N >= message_size);

    // Copy input to block bytes. For that we'll need at least input bytes (N)
    // but we want it to be padded to a multiple of BLOCK_SIZE_IN_BYTES.
    let mut block_bytes = [0; ((N / BLOCK_SIZE_IN_BYTES) + 1) * BLOCK_SIZE_IN_BYTES];
    if is_unconstrained() {
        for i in 0..message_size {
            block_bytes[i] = input[i];
        }
    } else {
        for i in 0..N {
            if i < message_size {
                block_bytes[i] = input[i];
            }
        }
    }

    //1. format_input_lanes
    let max_blocks = (N + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES;
    //maximum number of bytes to hash
    let real_max_blocks = (message_size + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES;
    let real_blocks_bytes = real_max_blocks * BLOCK_SIZE_IN_BYTES;

    block_bytes[message_size] = 1;
    block_bytes[real_blocks_bytes - 1] = 0x80;

    // populate a vector of 64-bit limbs from our byte array
    let mut sliced_buffer =
        [0; (((N / BLOCK_SIZE_IN_BYTES) + 1) * BLOCK_SIZE_IN_BYTES) / WORD_SIZE];
    for i in 0..sliced_buffer.len() {
        let limb_start = WORD_SIZE * i;

        let mut sliced = 0;
        let mut v = 1;
        for k in 0..WORD_SIZE {
            sliced += v * (block_bytes[limb_start + k] as Field);
            v *= 256;
        }

        sliced_buffer[i] = sliced as u64;
    }

    //2. sponge_absorb
    let mut state: [u64; NUM_KECCAK_LANES] = [0; NUM_KECCAK_LANES];
    // When in an unconstrained runtime we can take advantage of runtime loop bounds,
    // thus allowing us to simplify the loop body.
    if is_unconstrained() {
        for i in 0..real_max_blocks {
            if (i == 0) {
                for j in 0..LIMBS_PER_BLOCK {
                    state[j] = sliced_buffer[j];
                }
            } else {
                for j in 0..LIMBS_PER_BLOCK {
                    state[j] = state[j] ^ sliced_buffer[i * LIMBS_PER_BLOCK + j];
                }
            }
            state = keccakf1600(state);
        }
    } else {
        // `real_max_blocks` is guaranteed to at least be `1`
        // We peel out the first block as to avoid a conditional inside of the loop.
        // Otherwise, a dynamic predicate can cause a blowup in a constrained runtime.
        for j in 0..LIMBS_PER_BLOCK {
            state[j] = sliced_buffer[j];
        }
        state = keccakf1600(state);
        for i in 1..max_blocks {
            if i < real_max_blocks {
                for j in 0..LIMBS_PER_BLOCK {
                    state[j] = state[j] ^ sliced_buffer[i * LIMBS_PER_BLOCK + j];
                }
                state = keccakf1600(state);
            }
        }
    }

    //3. sponge_squeeze
    let mut result = [0; 32];
    for i in 0..4 {
        let lane = state[i] as Field;
        let lane_le: [u8; 8] = lane.to_le_bytes();
        for j in 0..8 {
            result[8 * i + j] = lane_le[j];
        }
    }
    result
}
*)

Definition keccak256
    (is_unconstrained : bool)
    {N : U32.t} (input : Array.t U8.t N) (message_size : U32.t) :
    Array.t U8.t {| Integer.value := 32 |}.
Admitted.
