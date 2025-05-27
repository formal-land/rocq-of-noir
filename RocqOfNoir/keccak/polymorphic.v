Require Import RocqOfNoir.RocqOfNoir.
Require Import simulation.RocqOfNoir.
Require Import keccak.monomorphic.

(** This module provides helpers to show the equality to debug [reflexivity] when it is too long or
    failing *)
Module Eq.
  Lemma LowLet {A : Set} (e e' : LowM.t A) k k'
      (H_e : e = e')
      (H_k : forall x, k x = k' x) :
    LowM.Let e k = LowM.Let e' k'.
  Proof.
    rewrite H_e.
    replace k with k' by now apply functional_extensionality.
    reflexivity.
  Qed.

  Lemma LetMinus {A : Set} (e1 e1' : LowM.t A) (e2 e2' : A -> LowM.t A)
      (H_e1 : e1 = e1')
      (H_e2 : forall x, e2 x = e2' x) :
    LowM.let_ e1 e2 = LowM.let_ e1' e2'.
  Proof.
    rewrite H_e1.
    replace e2 with e2' by now apply functional_extensionality.
    reflexivity.
  Qed.

  Lemma LetStar e1 e1' e2 e2'
      (H_e1 : e1 = e1')
      (H_e2 : forall x, e2 x = e2' x) :
    M.let_ e1 e2 = M.let_ e1' e2'.
  Proof.
    rewrite H_e1.
    replace e2 with e2' by now apply functional_extensionality.
    reflexivity.
  Qed.

  Lemma LetTilde e1 e1' e2 e2'
      (H_e1 : e1 = e1')
      (H_e2 : forall x, e2 x = e2' x) :
    M.let_strong e1 e2 = M.let_strong e1' e2'.
  Proof.
    rewrite H_e1.
    replace e2 with e2' by now apply functional_extensionality.
    reflexivity.
  Qed.

  Lemma If e e' t t' f f'
      (H_e : e = e')
      (H_t : t = t')
      (H_f : f = f') :
    M.if_ e t f = M.if_ e' t' f'.
  Proof.
    f_equal; assumption.
  Qed.

  Ltac tactic :=
    repeat (
      intro ||
      apply LowLet ||
      apply LetMinus ||
      apply LetStar ||
      apply LetTilde ||
      apply If
    ).
End Eq.

Definition keccak256 (N : U32.t) (α : list Value.t) : M.t :=
  match α with
  | [input; message_size] =>
    let input := M.alloc input in
    let message_size := M.alloc message_size in
    let* result :=
      do~ [[
        M.alloc (M.assert (|
          Binary.greater_equal (|
            to_value N,
            M.read (| message_size |)
          |),
          None
        |))
      ]] in
      let~ block_bytes := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.if_ (|
          M.call_closure (|
            M.read (| Builtin.is_unconstrained |),
            []
          |),
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| message_size |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    block_bytes,
                    M.read (| i |)
                  |),
                  M.read (| M.index (|
                    input,
                    M.read (| i |)
                  |) |)
                |))
              ]]
            |)
          ]],
          (Some ([[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              to_value N,
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Binary.less (|
                    M.read (| i |),
                    M.read (| message_size |)
                  |),
                  [[
                    M.alloc (M.write (|
                      M.index (|
                        block_bytes,
                        M.read (| i |)
                      |),
                      M.read (| M.index (|
                        input,
                        M.read (| i |)
                      |) |)
                    |))
                  ]],
                  None
                |)
              ]]
            |)
          ]]))
        |)
      ]] in
      let~ max_blocks := [[ M.copy (|
        M.alloc (Binary.divide (|
          Binary.add (|
            to_value N,
            get_global "BLOCK_SIZE_IN_BYTES" 0
          |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      let~ real_max_blocks := [[ M.copy (|
        M.alloc (Binary.divide (|
          Binary.add (|
            M.read (| message_size |),
            get_global "BLOCK_SIZE_IN_BYTES" 0
          |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      let~ real_blocks_bytes := [[ M.copy (|
        M.alloc (Binary.multiply (|
          M.read (| real_max_blocks |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      do~ [[
        M.alloc (M.write (|
          M.index (|
            block_bytes,
            M.read (| message_size |)
          |),
          Value.Integer IntegerKind.U8 1
        |))
      ]] in
      do~ [[
        M.alloc (M.write (|
          M.index (|
            block_bytes,
            Binary.subtract (|
              M.read (| real_blocks_bytes |),
              to_value N
            |)
          |),
          Value.Integer IntegerKind.U8 128
        |))
      ]] in
      let~ sliced_buffer := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| sliced_buffer |)
            ]
          |),
          fun (i : Value.t) =>
          let~ limb_start := [[ M.copy (|
            M.alloc (Binary.multiply (|
              get_global "WORD_SIZE" 1,
              M.read (| i |)
            |))
          |) ]] in
          let~ sliced := [[ M.copy_mutable (|
            M.alloc (Value.Field 0)
          |) ]] in
          let~ v := [[ M.copy_mutable (|
            M.alloc (Value.Field 1)
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              get_global "WORD_SIZE" 1,
              fun (k : Value.t) =>
              do~ [[
                M.alloc (M.write (|
                  sliced,
                  Binary.add (|
                    M.read (| sliced |),
                    Binary.multiply (|
                      M.read (| v |),
                      M.cast_to_field (|
                        M.read (| M.index (|
                          block_bytes,
                          Binary.add (|
                            M.read (| limb_start |),
                            M.read (| k |)
                          |)
                        |) |)
                      |)
                    |)
                  |)
                |))
              ]] in
              [[
                M.alloc (M.write (|
                  v,
                  Binary.multiply (|
                    M.read (| v |),
                    Value.Field 256
                  |)
                |))
              ]]
            |)
          ]] in
          [[
            M.alloc (M.write (|
              M.index (|
                sliced_buffer,
                M.read (| i |)
              |),
              M.cast (|
                M.read (| sliced |),
                IntegerKind.U64
              |)
            |))
          ]]
        |)
      ]] in
      [[
        sliced_buffer
      ]] in
    M.read result
      (* let~ state := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0
        ])
      |) ]] in
      do~ [[
        M.if_ (|
          M.call_closure (|
            M.read (| Builtin.is_unconstrained |),
            []
          |),
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| real_max_blocks |),
              fun (i : Value.t) =>
              do~ [[
                M.if_ (|
                  Binary.equal (|
                    M.read (| i |),
                    Value.Integer IntegerKind.U32 0
                  |),
                  [[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          M.read (| M.index (|
                            sliced_buffer,
                            M.read (| j |)
                          |) |)
                        |))
                      ]]
                    |)
                  ]],
                  (Some ([[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          Binary.xor (|
                            M.read (| M.index (|
                              state,
                              M.read (| j |)
                            |) |),
                            M.read (| M.index (|
                              sliced_buffer,
                              Binary.add (|
                                Binary.multiply (|
                                  M.read (| i |),
                                  get_global "LIMBS_PER_BLOCK" 2
                                |),
                                M.read (| j |)
                              |)
                            |) |)
                          |)
                        |))
                      ]]
                    |)
                  ]]))
                |)
              ]] in
              [[
                M.alloc (M.write (|
                  state,
                  M.call_closure (|
                    get_low_level "keccakf1600",
                    [
                      M.read (| state |)
                    ]
                  |)
                |))
              ]]
            |)
          ]],
          (Some (do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              get_global "LIMBS_PER_BLOCK" 2,
              fun (j : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    state,
                    M.read (| j |)
                  |),
                  M.read (| M.index (|
                    sliced_buffer,
                    M.read (| j |)
                  |) |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.alloc (M.write (|
              state,
              M.call_closure (|
                get_low_level "keccakf1600",
                [
                  M.read (| state |)
                ]
              |)
            |))
          ]] in
          [[
            M.for_ (|
              to_value N,
              M.read (| max_blocks |),
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Binary.less (|
                    M.read (| i |),
                    M.read (| real_max_blocks |)
                  |),
                  do~ [[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          Binary.xor (|
                            M.read (| M.index (|
                              state,
                              M.read (| j |)
                            |) |),
                            M.read (| M.index (|
                              sliced_buffer,
                              Binary.add (|
                                Binary.multiply (|
                                  M.read (| i |),
                                  get_global "LIMBS_PER_BLOCK" 2
                                |),
                                M.read (| j |)
                              |)
                            |) |)
                          |)
                        |))
                      ]]
                    |)
                  ]] in
                  [[
                    M.alloc (M.write (|
                      state,
                      M.call_closure (|
                        get_low_level "keccakf1600",
                        [
                          M.read (| state |)
                        ]
                      |)
                    |))
                  ]],
                  None
                |)
              ]]
            |)
          ]]))
        |)
      ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          Value.Integer IntegerKind.U32 4,
          fun (i : Value.t) =>
          let~ lane := [[ M.copy (|
            M.alloc (M.cast_to_field (|
              M.read (| M.index (|
                state,
                M.read (| i |)
              |) |)
            |))
          |) ]] in
          let~ lane_le := [[ M.copy (|
            M.alloc (M.call_closure (|
              get_function "to_le_bytes" 0,
              [
                M.read (| lane |)
              ]
            |))
          |) ]] in
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Value.Integer IntegerKind.U32 8,
              fun (j : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    result,
                    Binary.add (|
                      Binary.multiply (|
                        Value.Integer IntegerKind.U32 8,
                        M.read (| i |)
                      |),
                      M.read (| j |)
                    |)
                  |),
                  M.read (| M.index (|
                    lane_le,
                    M.read (| j |)
                  |) |)
                |))
              ]]
            |)
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result *)
  | _ => M.impossible "wrong number of arguments"
  end.

(* Lemma eq_keccak256₀ :
  get_function "keccak256" 0 = closure (keccak256 {| Integer.value := 1 |}).
Proof.
  autorewrite with get_function; apply f_equal.
  apply functional_extensionality; intro α.
  unfold keccak256₀.
  reflexivity.
Qed.
Global Hint Rewrite eq_keccak256₀ : get_function_eq. *)
