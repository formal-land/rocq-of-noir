Require Import RocqOfNoir.RocqOfNoir.
Require Import RocqOfNoir.proof.RocqOfNoir.
Require Import RocqOfNoir.simulation.RocqOfNoir.
Require Import RocqOfNoir.keccak.polymorphic.

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

Parameter for_loop : forall {A : Set} (acc : A) (start end_ : Z) (body : A -> Z -> M! A), M! A.

Lemma run_for_loop {State Address : Set} `{State.Trait State Address} (p : Z)
    {A : Set} `{ToValue A}
    (acc_in : A) (state_in : State)
    (start end_ : Z)
    (body : A -> Z -> M! A) (source_body : Z -> M.t)
    (P_A : A -> State -> Prop)
    (H_state_in : P_A acc_in state_in) :
  (forall acc state i,
    P_A acc state ->
    let output := body acc i in
    let P_state_out state_out :=
      match output with
      | Panic.Error => True
      | Panic.Success acc_out =>
        P_A acc_out state_out
      end in
    {{ p, state ⏩
      source_body i 🔽
      Panic.to_result (body acc i)
    ⏩ P_state_out }}
  ) ->
  let output := for_loop acc_in start end_ body in
  let P_state_out state_out :=
    match output with
    | Panic.Error => True
    | Panic.Success acc_out =>
      P_A acc_out state_out
    end in
  {{ p, state_in ⏩
    M.for_Z start end_ source_body 🔽
    Panic.to_result output
  ⏩ P_state_out }}.
Proof.
Admitted.

(* pub fn keccak256<let N: u32>(input: [u8; N], message_size: u32) -> [u8; 32] *)
Definition keccak256 (p : Z) {N : U32.t}
    (input : Array.t U8.t N) (message_size : U32.t) :
    M! _ :=
  (* assert(N >= message_size); *)
  let! _ := Panic.assert (N.(Integer.value) >=? message_size.(Integer.value)) in

  (*
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
  *)
  let block_bytes : Array.t U8.t _ :=
    Array.repeat
      {| Integer.value := (N.(Integer.value) / BLOCK_SIZE_IN_BYTES + 1) * BLOCK_SIZE_IN_BYTES |}
      {| Integer.value := 0 |} in
  let! block_bytes :=
    for_loop
      block_bytes
      0
      message_size.(Integer.value)
      (fun acc i =>
        let! element := Array.read input i in
        Array.write acc i element
      ) in

  (*
  let max_blocks = (N + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES;
  //maximum number of bytes to hash
  let real_max_blocks = (message_size + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES;
  let real_blocks_bytes = real_max_blocks * BLOCK_SIZE_IN_BYTES;
  *)
  let max_blocks := (N.(Integer.value) + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES in
  let real_max_blocks := (message_size.(Integer.value) + BLOCK_SIZE_IN_BYTES) / BLOCK_SIZE_IN_BYTES in
  let real_blocks_bytes := real_max_blocks * BLOCK_SIZE_IN_BYTES in

  (*
  block_bytes[message_size] = 1;
  block_bytes[real_blocks_bytes - 1] = 0x80;
  *)
  let! block_bytes := Array.write block_bytes message_size.(Integer.value) {| Integer.value := 1 |} in
  let! block_bytes := Array.write block_bytes (real_blocks_bytes - 1) {| Integer.value := 0x80 |} in

  (*
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
  *)
  let sliced_buffer_len := (((N.(Integer.value) / BLOCK_SIZE_IN_BYTES) + 1) * BLOCK_SIZE_IN_BYTES) / WORD_SIZE in
  let sliced_buffer : Array.t Field.t _ :=
    Array.repeat
      {| Integer.value := sliced_buffer_len |}
      {| Field.value := 0 |} in
  let! sliced_buffer :=
    for_loop
      sliced_buffer
      0
      sliced_buffer_len
      (fun sliced_buffer i =>
        let limb_start := WORD_SIZE * i in

        let sliced := {| Field.value := 0 |} in
        let v := {| Field.value := 1 |} in
        let! (sliced, v) :=
          for_loop
            (sliced, v)
            0
            WORD_SIZE
            (fun '(sliced, v) k =>
              let! element := Array.read block_bytes (limb_start + k) in
              let! element := Field.cast p element in
              return! (
                Field.add p sliced (Field.mul p v element),
                Field.add p v {| Field.value := 256 |}
            )
            ) in
        Array.write sliced_buffer i sliced
      ) in

  return! sliced_buffer.

Module State.
  Record t : Set := {
    block_bytes : option Value.t;
    sliced_buffer : option Value.t;
    sliced : option Value.t;
    v : option Value.t;
  }.

  Definition empty : t := {|
    block_bytes := None;
    sliced_buffer := None;
    sliced := None;
    v := None;
  |}.
End State.

Module Address.
  Inductive t : Set :=
  | BlockBytes
  | SlicedBuffer
  | Sliced
  | V.
End Address.

Instance Impl_State_for_State : State.Trait State.t Address.t := {
  read state address :=
    match address with
    | Address.BlockBytes => state.(State.block_bytes)
    | Address.SlicedBuffer => state.(State.sliced_buffer)
    | Address.Sliced => state.(State.sliced)
    | Address.V => state.(State.v)
    end;
  alloc_write state address value :=
    match address with
    | Address.BlockBytes => Some (state <| State.block_bytes := Some value |>)
    | Address.SlicedBuffer => Some (state <| State.sliced_buffer := Some value |>)
    | Address.Sliced => Some (state <| State.sliced := Some value |>)
    | Address.V => Some (state <| State.v := Some value |>)
    end;
}.

Lemma RunLetPanic {State Address : Set} `{State.Trait State Address} (p : Z)
    {A B : Set} `{ToValue A} `{ToValue B}
    (e : M.t) (e' : M! A)
    (k : Result.t -> M.t) (k' : A -> M! B)
    (state_in : State)
    (P_state_inter P_state_out : State -> Prop) :
  {{ p, state_in ⏩
    e 🔽 Panic.to_result e'
  ⏩ P_state_inter }} ->
  (forall (state_inter : State) (output_inter : A),
    P_state_inter state_inter ->
    {{ p, state_inter ⏩
      k (Result.Ok (to_value output_inter)) 🔽 Panic.to_result (k' output_inter)
    ⏩ P_state_out }}
  ) ->
  (k Result.Panic = LowM.Pure Result.Panic) ->
  P_state_out 
  {{ p, state_in ⏩
    LowM.Let e k 🔽 Panic.to_result (Panic.bind e' k')
  ⏩ P_state_out }}.
Proof.
  intros H_e H_k H_k_panic.
  eapply Run.Let; cbn. {
    apply H_e.
  }
  intros state_inter H_state_inter.
  destruct e'; cbn in *.
  { now apply H_k. }
  { rewrite H_k_panic.
    apply Run.Pure.
  }
  eapply H_k.
  - exact state_in.
  - exact (to_value e').

Lemma run_keccak256
    (p : Z)
    {N : U32.t}
    (input : Array.t U8.t N) (message_size : U32.t)
    (H_unconstrained :
      [[ M.call_closure (|
        M.read (| Builtin.is_unconstrained |),
        []
      |) ]] =
      M.pure (Value.Bool true)
    )
    (H_message_size : message_size.(Integer.value) <= N.(Integer.value)) :
  let output := keccak256 p input message_size in
  let P_state_out state_out :=
    match output with
    | Panic.Error => True
    | Panic.Success sliced_buffer =>
      state_out.(State.sliced_buffer) = Some (to_value sliced_buffer)
    end in
  {{ p, State.empty ⏩
    polymorphic.keccak256 N [to_value input; to_value message_size] 🔽
    Panic.to_result output
  ⏩ P_state_out }}.
Proof.
  unfold polymorphic.keccak256, keccak256.
  progress repeat rewrite H_unconstrained.
  eapply Run.Let; cbn. {
    destruct (_ >=? _) eqn:?; [|lia]; cbn.
    apply Run.PureExact.
  }
  intros ? ->; cbn.
  eapply Run.Let; cbn. {
    eapply Run.CallPrimitiveStateAlloc with (address := Address.BlockBytes); try reflexivity.
    unfold set.
    apply Run.PureExact.
  }
  intros ? ->; cbn.
  eapply Run.Let; cbn. {
    apply run_for_loop. with (acc_in :=).
  cbn in H_unconstrained.
  rewrite H_unconstrained; cbn.
  cbn.
