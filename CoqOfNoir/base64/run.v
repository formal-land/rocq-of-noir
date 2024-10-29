Require Import CoqOfNoir.CoqOfNoir.
Require CoqOfNoir.base64.translation.

Import Run.

Module U8.
  Inductive t : Set :=
  | Make (z : Z).

  Definition to_value (i : t) : Value.t :=
    let 'U8.Make i := i in
    Value.Integer i.
End U8.

Module Eq.
  Class Trait (Self : Set) : Set := {
    eq : Self -> Self -> bool;
  }.
End Eq.

Global Instance Eq_for_U8 : Eq.Trait U8.t := {
  Eq.eq (self other : U8.t) :=
    let 'U8.Make self := self in
    let 'U8.Make other := other in
    self =? other;
}.

Lemma run_eq₅ {State Address : Set} `{State.Trait State Address}
    (state : State) (self other : U8.t) :
  {{ state |
    translation.eq₅ [U8.to_value self; U8.to_value other] ⇓
    Result.Ok (Value.Bool (Eq.eq self other))
  | state }}.
Proof.
  unfold translation.eq₅.
  destruct self as [self], other as [other]; cbn.
  destruct (self =? other) eqn:H_eq; cbn.
  { apply Run.CallPrimitiveIsEqualTrue; [f_equal; lia|].
    apply Run.Pure.
  }
  { apply Run.CallPrimitiveIsEqualFalse. {
      assert (self <> other) by lia.
      congruence.
    }
    apply Run.Pure.
  }
Qed.
