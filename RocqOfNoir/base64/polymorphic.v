Require Import RocqOfNoir.RocqOfNoir.
Require Import simulation.RocqOfNoir.
Require Import base64.monomorphic.

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

Module Field.
  Definition to_be_radix (N : U32.t) (α : list Value.t) : M.t :=
    match α with
    | [self; radix] =>
      let self := M.alloc self in
      let radix := M.alloc radix in
      let* result :=
        do~ [[
          M.alloc (M.call_closure (|
            M.read (| Builtin.assert_constant |),
            [
              M.read (| radix |)
            ]
          |))
        ]] in
        [[
          M.alloc (M.call_closure (|
            M.read (| Builtin.__to_be_radix |),
            [
              M.read (| self |);
              M.read (| radix |)
            ]
          |))
        ]] in
      M.read result
    | _ => M.impossible "wrong number of arguments"
    end.

  Lemma eq_to_be_radix₁ : get_function "to_be_radix" 1 = closure (to_be_radix {| Integer.value := 40 |}).
  Proof.
    autorewrite with get_function; f_equal.
  Qed.
  Global Hint Rewrite eq_to_be_radix₁ : get_function_eq.
End Field.

Module Base64EncodeBE.
  Record t : Set := {
    table : Array.t U8.t {| Integer.value := 64 |};
  }.

  Definition new (α : list Value.t) : M.t :=
    match α with
  | [] =>
      let* result :=
        [[
          let~ table := [[ M.copy (|
            M.alloc (Value.Array [
              Value.Integer IntegerKind.U8 65;
              Value.Integer IntegerKind.U8 66;
              Value.Integer IntegerKind.U8 67;
              Value.Integer IntegerKind.U8 68;
              Value.Integer IntegerKind.U8 69;
              Value.Integer IntegerKind.U8 70;
              Value.Integer IntegerKind.U8 71;
              Value.Integer IntegerKind.U8 72;
              Value.Integer IntegerKind.U8 73;
              Value.Integer IntegerKind.U8 74;
              Value.Integer IntegerKind.U8 75;
              Value.Integer IntegerKind.U8 76;
              Value.Integer IntegerKind.U8 77;
              Value.Integer IntegerKind.U8 78;
              Value.Integer IntegerKind.U8 79;
              Value.Integer IntegerKind.U8 80;
              Value.Integer IntegerKind.U8 81;
              Value.Integer IntegerKind.U8 82;
              Value.Integer IntegerKind.U8 83;
              Value.Integer IntegerKind.U8 84;
              Value.Integer IntegerKind.U8 85;
              Value.Integer IntegerKind.U8 86;
              Value.Integer IntegerKind.U8 87;
              Value.Integer IntegerKind.U8 88;
              Value.Integer IntegerKind.U8 89;
              Value.Integer IntegerKind.U8 90;
              Value.Integer IntegerKind.U8 97;
              Value.Integer IntegerKind.U8 98;
              Value.Integer IntegerKind.U8 99;
              Value.Integer IntegerKind.U8 100;
              Value.Integer IntegerKind.U8 101;
              Value.Integer IntegerKind.U8 102;
              Value.Integer IntegerKind.U8 103;
              Value.Integer IntegerKind.U8 104;
              Value.Integer IntegerKind.U8 105;
              Value.Integer IntegerKind.U8 106;
              Value.Integer IntegerKind.U8 107;
              Value.Integer IntegerKind.U8 108;
              Value.Integer IntegerKind.U8 109;
              Value.Integer IntegerKind.U8 110;
              Value.Integer IntegerKind.U8 111;
              Value.Integer IntegerKind.U8 112;
              Value.Integer IntegerKind.U8 113;
              Value.Integer IntegerKind.U8 114;
              Value.Integer IntegerKind.U8 115;
              Value.Integer IntegerKind.U8 116;
              Value.Integer IntegerKind.U8 117;
              Value.Integer IntegerKind.U8 118;
              Value.Integer IntegerKind.U8 119;
              Value.Integer IntegerKind.U8 120;
              Value.Integer IntegerKind.U8 121;
              Value.Integer IntegerKind.U8 122;
              Value.Integer IntegerKind.U8 48;
              Value.Integer IntegerKind.U8 49;
              Value.Integer IntegerKind.U8 50;
              Value.Integer IntegerKind.U8 51;
              Value.Integer IntegerKind.U8 52;
              Value.Integer IntegerKind.U8 53;
              Value.Integer IntegerKind.U8 54;
              Value.Integer IntegerKind.U8 55;
              Value.Integer IntegerKind.U8 56;
              Value.Integer IntegerKind.U8 57;
              Value.Integer IntegerKind.U8 43;
              Value.Integer IntegerKind.U8 47
            ])
          |) ]] in
          [[
            M.alloc (Value.Tuple [M.read (| table |)])
          ]]
        ]] in
      M.read result
    | _ => M.impossible "wrong number of arguments"
    end.

  Lemma eq_new₁ : get_function "new" 1 = closure new.
  Proof.
    autorewrite with get_function; f_equal.
  Qed.
  Global Hint Rewrite eq_new₁ : get_function_eq.

  Definition get (α : list Value.t) : M.t :=
    match α with
  | [self; idx] =>
    let self := M.alloc self in
    let idx := M.alloc idx in
    let* result :=
      [[
        M.index (|
          M.extract_tuple_field (|
              self,
            0
          |),
          M.read (| idx |)
        |)
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

  Lemma eq_get₁ : get_function "get" 1 = closure get.
  Proof.
    autorewrite with get_function; apply f_equal.
    reflexivity.
  Qed.
  Global Hint Rewrite eq_get₁ : get_function_eq.
End Base64EncodeBE.

Definition base64_encode_elements (InputElements : U32.t) (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Encoder := [[ M.copy_mutable (|
        M.alloc (M.call_closure (|
          closure Base64EncodeBE.new,
          []
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array (
          List.repeat (Value.Integer IntegerKind.U8 0) (Z.to_nat InputElements.(Integer.value))
        ))
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          to_value InputElements,
          fun (i : Value.t) =>
          [[
            M.alloc (M.write (|
              M.index (|
                result,
                M.read (| i |)
              |),
              M.call_closure (|
                closure Base64EncodeBE.get,
                [
                  M.read (| Base64Encoder |);
                  M.cast (|
                    M.read (| M.index (|
                      input,
                      M.read (| i |)
                    |) |),
                    IntegerKind.Field
                  |)
                ]
              |)
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Lemma eq_base64_encode_elements₀ :
  get_function "base64_encode_elements" 0 = closure (base64_encode_elements {| Integer.value := 118 |}).
Proof.
  autorewrite with get_function; apply f_equal.
  apply functional_extensionality; intro α.
  unfold base64_encode_elements₀.
  autorewrite with get_function_eq.
  reflexivity.
Qed.
Global Hint Rewrite eq_base64_encode_elements₀ : get_function_eq.

Definition base64_encode (InputBytes OutputElements : U32.t) (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array (List.repeat
          (Value.Integer IntegerKind.U8 0)
          (Z.to_nat OutputElements.(Integer.value))
        ))
      |) ]] in
      let~ BASE64_ELEMENTS_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 40)
      |) ]] in
      let~ BYTES_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 30)
      |) ]] in
      let~ num_chunks := [[ M.copy (|
        M.alloc (Binary.add (|
          Binary.divide (|
            to_value InputBytes,
            M.read (| BYTES_PER_CHUNK |)
          |),
          M.cast (|
            Binary.not_equal (|
              Binary.modulo (|
                to_value InputBytes,
                M.read (| BYTES_PER_CHUNK |)
              |),
              Value.Integer IntegerKind.U32 0
            |),
            IntegerKind.U32
          |)
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          Binary.greater (|
            M.read (| num_chunks |),
            Value.Integer IntegerKind.U32 0
          |),
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Binary.subtract (|
                M.read (| num_chunks |),
                Value.Integer IntegerKind.U32 1
              |),
              fun (i : Value.t) =>
              let~ slice := [[ M.copy_mutable (|
                M.alloc (Value.Integer IntegerKind.Field 0)
              |) ]] in
              do~ [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BYTES_PER_CHUNK |),
                  fun (j : Value.t) =>
                  do~ [[
                    M.alloc (M.write (|
                      slice,
                      Binary.multiply (|
                        M.read (| slice |),
                        Value.Integer IntegerKind.Field 256
                      |)
                    |))
                  ]] in
                  [[
                    M.alloc (M.write (|
                      slice,
                      Binary.add (|
                        M.read (| slice |),
                        M.cast (|
                          M.read (| M.index (|
                            input,
                            Binary.add (|
                              Binary.multiply (|
                                M.read (| i |),
                                M.read (| BYTES_PER_CHUNK |)
                              |),
                              M.read (| j |)
                            |)
                          |) |),
                          IntegerKind.Field
                        |)
                      |)
                    |))
                  ]]
                |)
              ]] in
              let~ slice_base64_chunks := [[ M.copy (|
                M.alloc (M.call_closure (|
                  closure (Field.to_be_radix {| Integer.value := 30 |}),
                  [
                    M.read (| slice |);
                    Value.Integer IntegerKind.U32 64
                  ]
                |))
              |) ]] in
              [[
                M.for_ (|
                  Value.Integer IntegerKind.U32 0,
                  M.read (| BASE64_ELEMENTS_PER_CHUNK |),
                  fun (j : Value.t) =>
                  [[
                    M.alloc (M.write (|
                      M.index (|
                        result,
                        Binary.add (|
                          Binary.multiply (|
                            M.read (| i |),
                            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |),
                      M.read (| M.index (|
                        slice_base64_chunks,
                        M.read (| j |)
                      |) |)
                    |))
                  ]]
                |)
              ]]
            |)
          ]] in
          let~ bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              to_value InputBytes,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BYTES_PER_CHUNK |)
              |)
            |))
          |) ]] in
          let~ slice := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| bytes_in_final_chunk |),
              fun (j : Value.t) =>
              do~ [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 256
                  |)
                |))
              ]] in
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.add (|
                    M.read (| slice |),
                    M.cast (|
                      M.read (| M.index (|
                        input,
                        Binary.add (|
                          Binary.multiply (|
                            Binary.subtract (|
                              M.read (| num_chunks |),
                              Value.Integer IntegerKind.U32 1
                            |),
                            M.read (| BYTES_PER_CHUNK |)
                          |),
                          M.read (| j |)
                        |)
                      |) |),
                      IntegerKind.Field
                    |)
                  |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.for_ (|
              M.read (| bytes_in_final_chunk |),
              M.read (| BYTES_PER_CHUNK |),
              fun (_ : Value.t) =>
              [[
                M.alloc (M.write (|
                  slice,
                  Binary.multiply (|
                    M.read (| slice |),
                    Value.Integer IntegerKind.Field 256
                  |)
                |))
              ]]
            |)
          ]] in
          let~ slice_base64_chunks := [[ M.copy (|
            M.alloc (M.call_closure (|
              closure (Field.to_be_radix {| Integer.value := 30 |}),
              [
                M.read (| slice |);
                Value.Integer IntegerKind.U32 64
              ]
            |))
          |) ]] in
          let~ num_elements_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              to_value OutputElements,
              Binary.multiply (|
                Binary.subtract (|
                  M.read (| num_chunks |),
                  Value.Integer IntegerKind.U32 1
                |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| num_elements_in_final_chunk |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    result,
                    Binary.add (|
                      Binary.multiply (|
                        Binary.subtract (|
                          M.read (| num_chunks |),
                          Value.Integer IntegerKind.U32 1
                        |),
                        M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                      |),
                      M.read (| i |)
                    |)
                  |),
                  M.read (| M.index (|
                    slice_base64_chunks,
                    M.read (| i |)
                  |) |)
                |))
              ]]
            |)
          ]] in
          [[
            M.alloc (M.write (|
              result,
              M.call_closure (|
                closure (base64_encode_elements {| Integer.value := 118 |}),
                [
                  M.read (| result |)
                ]
              |)
            |))
          ]],
          None
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Lemma eq_base64_encode₀ :
  get_function "base64_encode" 0 = closure (base64_encode {| Integer.value := 88 |} {| Integer.value := 118 |}).
Proof.
  autorewrite with get_function; apply f_equal.
  apply functional_extensionality; intro α.
  unfold base64_encode₀.
  autorewrite with get_function_eq.
  destruct α as [|input α]; [reflexivity|].
  destruct α; [|reflexivity].
  apply Eq.LetStar; [reflexivity|intro result].
  reflexivity.
Qed.
