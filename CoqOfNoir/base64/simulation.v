Require Import CoqOfNoir.CoqOfNoir.
Require Import CoqOfNoir.proof.CoqOfNoir.
Require Import CoqOfNoir.simulation.CoqOfNoir.
Require CoqOfNoir.base64.polymorphic.

Import Run.

Module Base64EncodeBE.
  (*
  struct Base64EncodeBE {
      table: [u8; 64]
  }
  *)
  Record t : Set := {
    table : Array.t U8.t (U32.Make 64);
  }.

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (x : t) :=
      Value.Tuple [to_value x.(table)];
  }.

  (*
  /// Creates a new encoder that uses the standard Base64 Alphabet (base64) specified in RFC 4648 
  /// (https://datatracker.ietf.org/doc/html/rfc4648#section-4)
  fn new() -> Self {
      Base64EncodeBE {
          // The alphabet values here are standard UTF-8 (and ASCII) byte encodings, so the index
          // in the table is the 6-bit Base64 value, and the value at that index is the UTF-8 
          // encoding of that value.
          table: [
              65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,// 0-25 (A-Z)
              97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,// 26-51 (a-z)
              48, 49, 50, 51, 52, 53, 54, 55, 56, 57,// 0-9
              43,// +
              47// /
          ]
      }
  }
  *)
  Definition new : t := {|
    table := Array.Make (List.map U8.Make [
      65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90;
      97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122;
      48; 49; 50; 51; 52; 53; 54; 55; 56; 57;
      43;
      47
    ])
  |}.

  Lemma run_new {State Address : Set} `{State.Trait State Address}
      (p : Z) (state : State) :
    {{ p, state |
      polymorphic.Base64EncodeBE.new [] ⇓
      Result.Ok (to_value new)
    | state }}.
  Proof.
    unfold polymorphic.Base64EncodeBE.new, new.
    eapply Run.Let. {
      apply Run.Pure.
    }
    apply Run.Pure.
  Qed.

  (*
  fn get(self, idx: Field) -> u8 {
      self.table[idx]
  }
  *)
  Definition get (self : t) (idx : Field.t) : M! U8.t :=
    Array.read self.(table) idx.

  Lemma run_get {State Address : Set} `{State.Trait State Address}
      (p : Z) (state : State)
      (self : t) (idx : Field.t) (result : U8.t)
      (H_result : get self idx = return! result) :
    {{ p, state |
      polymorphic.Base64EncodeBE.get [to_value self; to_value idx] ⇓
      Result.Ok (to_value result)
    | state }}.
  Proof.
    unfold polymorphic.Base64EncodeBE.get.
    destruct self as [ [table] ], idx as [idx].
    cbn in *.
    rewrite List.nth_error_map.
    destruct List.nth_error; cbn.
    { inversion_clear H_result.
      apply Run.Pure.
    }
    { exfalso.
      discriminate.
    }
  Qed.
End Base64EncodeBE.

(*
/**
 * @brief Take an array of ASCII values and convert into base64 values
 **/
pub fn base64_encode_elements<let InputElements: u32>(input: [u8; InputElements]) -> [u8; InputElements] {
    // for some reason, if the lookup table is not defined in a struct, access costs are expensive and ROM tables aren't being used :/
    let mut Base64Encoder = Base64EncodeBE::new();

    let mut result: [u8; InputElements] = [0; InputElements];

    for i in 0..InputElements {
        result[i] = Base64Encoder.get(input[i] as Field);
    }
    result
}
*)
Definition base64_encode_elements {InputElements : U32.t} (input : Array.t U8.t InputElements) :
    M! (Array.t U8.t InputElements) :=
  let Base64Encoder := Base64EncodeBE.new in

  let result : Array.t U8.t InputElements := Array.repeat InputElements (U8.Make 0) in

  List.fold_left
    (fun (result : M! (Array.t U8.t InputElements)) (i : nat) =>
      let! result := result in
      let i : U32.t := U32.Make (Z.of_nat i) in
      let! input_i := Array.read input i in
      let! new_result_i := Base64EncodeBE.get Base64Encoder (Field.Make (Integer.to_Z input_i)) in
      Array.write result i new_result_i
    )
    (List.seq 0 (Z.to_nat (SemiInteger.to_Z InputElements)))
    (return! result).

Module base64_encode_elements.
  Module State.
    Record t : Set := {
      base64_encoder : option Value.t;
      result : option Value.t;
    }.
    Arguments t : clear implicits.

    Definition init : t := {|
      base64_encoder := None;
      result := None;
    |}.
  End State.

  Module Address.
    Inductive t : Set :=
    | Base64Encoder
    | Result.
  End Address.

  Global Instance Impl_State : State.Trait State.t Address.t := {
    read a s :=
      match a with
      | Address.Base64Encoder => s.(State.base64_encoder)
      | Address.Result => s.(State.result)
      end;
    alloc_write a s v :=
      match a with
      | Address.Base64Encoder => Some (s <| State.base64_encoder := Some v |>)
      | Address.Result => Some (s <| State.result := Some v |>)
      end;
  }.

  Lemma Impl_IsStateValid : State.Valid.t Impl_State.
  Proof.
    sauto.
  Qed.
End base64_encode_elements.

Lemma run_base64_encode_elements
    (p : Z)
    {InputElements : U32.t}
    (input : Array.t U8.t InputElements) (result : Array.t U8.t InputElements)
    (H_result : base64_encode_elements input = return! result) :
  {{ p, base64_encode_elements.State.init |
    polymorphic.base64_encode_elements InputElements [to_value input] ⇓
    Result.Ok (to_value result)
  | base64_encode_elements.State.init }}.
Proof.
  unfold polymorphic.base64_encode_elements.
  eapply Run.Let. {
    eapply Run.CallClosure. {
      apply Base64EncodeBE.run_new.
    }
    eapply CallPrimitiveStateAlloc with (address := base64_encode_elements.Address.Base64Encoder);
      try reflexivity.
    apply Run.Pure.
  }
  eapply Run.Let. {
    eapply CallPrimitiveStateAlloc with (address := base64_encode_elements.Address.Result);
      try reflexivity.
    apply Run.Pure.
  }
  fold @LowM.let_.
  apply Run.LetUnfold.
  fold @LowM.let_.
  
   {
    (* Entering the fold *)
    destruct input as [input].
  simpl.
    cbn.
      eapply Run.Let. {
        eapply Base64EncodeBE.run_new.
      }
      apply Run.Pure.
    }
    apply Base64EncodeBE.run_new.
  }
  unfold base64_encode_elements in H_result.

Qed.

(* Lemma run_eq₂ {State Address : Set} `{State.Trait State Address}
    (state : State) (self other : Array.t U8.t 36) :
  {{ state |
    translation.eq₂ [to_value self; to_value other] ⇓
    Result.Ok (to_value (Eq.eq self other))
  | state }}.
Proof.
  unfold translation.eq₂. *)

(*
pub fn base64_encode<let InputBytes: u32, let OutputElements: u32>(input: [u8; InputBytes]) -> [u8; OutputElements] {
    // 240 bits fits 40 6-bit chunks and 30 8-bit chunks
    // we pack 40 base64 values into a field element and convert into 30 bytes
    // TODO: once we support arithmetic ops on generics, derive OutputBytes from InputBytes
    let mut result: [u8; OutputElements] = [0; OutputElements];
    let BASE64_ELEMENTS_PER_CHUNK: u32 = 40;
    let BYTES_PER_CHUNK: u32 = 30;
    let num_chunks = (InputBytes / BYTES_PER_CHUNK) + (InputBytes % BYTES_PER_CHUNK != 0) as u32;

    if num_chunks > 0 {
        for i in 0..num_chunks - 1 {
            let mut slice: Field = 0;
            for j in 0..BYTES_PER_CHUNK {
                slice *= 256;
                slice += input[i * BYTES_PER_CHUNK + j] as Field;
            }

            let slice_base64_chunks: [u8; 40] = slice.to_be_radix(64);
            for j in 0..BASE64_ELEMENTS_PER_CHUNK {
                result[i * BASE64_ELEMENTS_PER_CHUNK + j] = slice_base64_chunks[j];
            }
        }

        let bytes_in_final_chunk = InputBytes - ((num_chunks - 1) * BYTES_PER_CHUNK);

        let mut slice: Field = 0;
        for j in 0..bytes_in_final_chunk {
            slice *= 256;
            slice += input[(num_chunks - 1) * BYTES_PER_CHUNK + j] as Field;
        }
        for _ in bytes_in_final_chunk..BYTES_PER_CHUNK {
            slice *= 256;
        }

        // TODO: check is it cheaper to use a constant value in `to_be_bytes` or can we use `bytes_in_final_chunk`?
        let slice_base64_chunks: [u8; 40] = slice.to_be_radix(64);

        let num_elements_in_final_chunk = OutputElements - ((num_chunks - 1) * BASE64_ELEMENTS_PER_CHUNK);
        for i in 0..num_elements_in_final_chunk {
            result[(num_chunks - 1) * BASE64_ELEMENTS_PER_CHUNK + i] = slice_base64_chunks[i];
        }
        result = base64_encode_elements(result);
    }

    result
}
*)
(* Definition base64_encode {InputBytes OutputElements : U32.t} (input : Array.t U8.t InputBytes) :
    Array.t U8.t OutputElements :=
  let result : Array.t U8.t OutputElements := Array.repeat OutputElements (U8.Make 0) in
  let BASE64_ELEMENTS_PER_CHUNK : U32.t := U32.Make 40 in
  let BYTES_PER_CHUNK : U32.t := U32.Make 30 in
  let num_chunks : U32.t :=
    Integer.add
      (Integer.div InputBytes BYTES_PER_CHUNK)
      (Integer.of_bool (negb (Eq.eq (Integer.mod_ InputBytes BYTES_PER_CHUNK) (U32.Make 0)))) in

  if Integer.to_Z num_chunks >? 0 then
    M.for_ () *)
