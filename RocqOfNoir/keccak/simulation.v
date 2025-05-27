Require Import RocqOfNoir.RocqOfNoir.
Require Import RocqOfNoir.proof.RocqOfNoir.
Require Import RocqOfNoir.simulation.RocqOfNoir.
Require Import RocqOfNoir.keccak.polymorphic.

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
    (inject_A : A -> State -> State)
    (H_state_in : inject_A acc_in state_in = state_in) :
  (forall acc state i,
    let state_in := inject_A acc state in
    let output :=
      match body acc i with
      | Some acc_out => Some (M.alloc (to_value tt), inject_A acc_out state_in)
      | None => None
      end in
    {{ p, state_in ⏩
      source_body i 🔽
      output
    }}
  ) ->
  let output :=
    match for_loop acc_in start end_ body with
    | Some acc_out => Some (M.alloc (to_value tt), inject_A acc_out state_in)
    | None => None
    end in
  {{ p, state_in ⏩
    M.for_Z start end_ source_body 🔽
    output
  }}.
Proof.
Admitted.

(* Here we define a simulation of the keccak256 function in Noir. *)

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
  let! block_bytes : Array.t U8.t _ := return! (
    Array.repeat
      {| Integer.value := (N.(Integer.value) / BLOCK_SIZE_IN_BYTES + 1) * BLOCK_SIZE_IN_BYTES |}
      {| Integer.value := 0 |}
   ) in
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

Definition apply_φ {State A : Set} (φ : A -> Value.t * (State -> State))
    (state_in : State) (value : A) :
    Value.t * State :=
  let '(value, inject_state) := φ value in
  (value, inject_state state_in).

Module Option.
  Definition map {A B : Set} (f : A -> B) (x : option A) : option B :=
    match x with
    | Some value => Some (f value)
    | None => None
    end.
End Option.

(** Auxiliary lemma that is useful to break down let definitions on the two sides (source code and
    simulation). *)
Lemma RunLetPanic {State Address : Set} `{State.Trait State Address} (p : Z)
    {A B : Set}
    (e : M.t) (e' : M! A)
    (φ_A : A -> Value.t * (State -> State))
    (k : Value.t -> M.t) (k' : A -> M! B)
    (map_B : B -> Value.t * State)
    (state_in : State) :
  {{ p, state_in ⏩
    e 🔽
    Option.map (apply_φ φ_A state_in) e'
  }} ->
  (forall (value' : A),
    let '(value, state_inter) := apply_φ φ_A state_in value' in
    {{ p, state_inter ⏩
      k value 🔽
      Option.map map_B (k' value')
    }}
  ) ->
  {{ p, state_in ⏩
    M.Let e k 🔽
    Option.map map_B (Panic.bind e' k')
  }}.
Proof.
  intros H_e H_k.
  eapply Run.Let; cbn. {
    apply H_e.
  }
  destruct e' as [value' |]; cbn in *; [|reflexivity].
  specialize (H_k value').
  destruct (φ_A value') as [value_inter inject_state].
  apply H_k.
Qed.

(** Here we show, for the beginning of the simulation, that we are equivalent to the translation of
    the source code. It is unfortunately still extremely verbose and tedious to write. The positive
    side is that the complexity of the proof follows the size of the code: there are no explosions
    due to the explosion of possible path combinations for example. *)
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
  let output :=
    match keccak256 p input message_size with
    | None => None
    | Some output => Some (to_value output, State.empty)
    end in
  {{ p, State.empty ⏩
    polymorphic.keccak256 N [to_value input; to_value message_size] 🔽
    output
  }}.
Proof.
  unfold polymorphic.keccak256, keccak256.
  progress repeat rewrite H_unconstrained.
  eapply RunLetPanic with (φ_A := fun _ => (
    M.alloc (to_value tt),
    fun state => state
  )). {
    cbn.
    destruct (_ >=? _) eqn:?; [|lia]; cbn.
    now apply Run.Pure.
  }
  intros [].
  eapply RunLetPanic with (φ_A := fun block_bytes => (
    Value.Pointer (Pointer.Mutable (Pointer.Mutable.Make Address.BlockBytes [])),
    fun state => state <| State.block_bytes := Some (to_value block_bytes) |>
  )). {
    cbn.
    eapply Run.CallPrimitiveStateAlloc with (address := Address.BlockBytes); try reflexivity.
    unfold set; cbn.
    apply Run.Pure.
    repeat f_equal.
    now rewrite List.map_repeat.
  }
  intros block_bytes.
  eapply RunLetPanic with (φ_A := fun block_bytes => (
    M.alloc (to_value tt),
    fun state => state <| State.block_bytes := Some (to_value block_bytes) |>
  )). {
    cbn.
    apply run_for_loop.
    { typeclasses eauto. }
    { reflexivity. }
    { intros acc state i.
      cbn.
      unfold Array.read.
      rewrite List.nth_error_map; cbn.
      destruct List.nth_error as [element |]; cbn; [|now apply Run.Panic].
      eapply Run.CallPrimitiveStateRead; [reflexivity |]; cbn.
      unfold Array.write.
      rewrite List.nth_error_map; cbn.
      match goal with
      | |- context[List.listUpdate_error ?l ?i ?v] =>
        pose proof (Array.list_nth_error_listUpdate_error l i v)
      end.
      destruct List.nth_error; cbn.
      { erewrite Array.listUpdate_error_map; [|reflexivity].
        destruct List.listUpdate_error; cbn; [|now apply Run.Panic].
        eapply Run.CallPrimitiveStateWrite; [reflexivity |]; cbn.
        now apply Run.Pure.
      }
      { destruct List.listUpdate_error; cbn; [easy |].
        now apply Run.Panic.
      }
    }
  }
  intros ?block_bytes.
  progress repeat (
    (replace Binary.add with Binary.add_unbounded by admit) ||
    (replace Binary.multiply with Binary.multiply_unbounded by admit) ||
    (replace Binary.divide with Binary.divide_unbounded by admit) ||
    (replace (get_global "BLOCK_SIZE_IN_BYTES" 0) with (Value.Integer IntegerKind.U32 BLOCK_SIZE_IN_BYTES) by admit) ||
    (replace (get_global "WORD_SIZE" 1) with (Value.Integer IntegerKind.U32 WORD_SIZE) by admit)
  ).
  do 3 apply LetUnfold.
  eapply RunLetPanic with (φ_A := fun block_bytes => (
    M.alloc (to_value tt),
    fun state => state <| State.block_bytes := Some (to_value block_bytes) |>
  )). {
    cbn.
    eapply Run.CallPrimitiveStateRead; [reflexivity |]; cbn.
    unfold Array.write.
    rewrite List.nth_error_map; cbn.
    match goal with
    | |- context[List.listUpdate_error ?l ?i ?v] =>
      pose proof (Array.list_nth_error_listUpdate_error l i v)
    end.
    destruct List.nth_error; cbn.
    { erewrite Array.listUpdate_error_map; [|instantiate (1 := Integer.Build_t _ _); reflexivity].
      destruct List.listUpdate_error; cbn; [|now apply Run.Panic].
      eapply Run.CallPrimitiveStateWrite; [reflexivity |]; cbn.
      now apply Run.Pure.
    }
    { destruct List.listUpdate_error; cbn; [easy |].
      now apply Run.Panic.
    }
  }
  intros ?block_bytes.
Admitted.
