Require Import CoqOfNoir.CoqOfNoir.

Module ToValue.
  Class Trait (Self : Set) : Set := {
    to_value : Self -> Value.t;
  }.
End ToValue.
Export ToValue.

Global Instance Impl_ToValue_for_bool : ToValue.Trait bool := {
  to_value (b : bool) :=
    Value.Bool b;
}.

Module Field.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.Field i;
  }.
End Field.

Module U1.
  Inductive t : Set :=
  | Make (i : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.U1 i;
  }.
End U1.

Module U8.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.U8 i;
  }.
End U8.

Module U16.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.U16 i;
  }.
End U16.

Module U32.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.U32 i;
  }.
End U32.

Module U64.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.U64 i;
  }.
End U64.

Module I1.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.I1 i;
  }.
End I1.

Module I8.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.I8 i;
  }.
End I8.

Module I16.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.I16 i;
  }.
End I16.

Module I32.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.I32 i;
  }.
End I32.

Module I64.
  Inductive t : Set :=
  | Make (z : Z).

  Global Instance Impl_ToValue : ToValue.Trait t := {
    to_value (i : t) :=
      let 'Make i := i in
      Value.Integer IntegerKind.I64 i;
  }.
End I64.

Module Integer.
  Class Trait (Self : Set) : Set := {
    to_Z : Self -> Z;
    of_Z : Z -> Self;
  }.

  Definition add {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (to_Z self + to_Z other).

  Definition sub {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (to_Z self - to_Z other).

  Definition mul {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (to_Z self * to_Z other).

  Definition div {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (to_Z self / to_Z other).

  Definition mod_ {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (to_Z self mod to_Z other).

  Definition of_bool {Self : Set} `{Trait Self} (b : bool) : Self :=
    of_Z (if b then 1 else 0).
End Integer.

Global Instance Impl_Integer_for_U1 : Integer.Trait U1.t := {
  Integer.to_Z (i : U1.t) :=
    let 'U1.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    U1.Make (i mod (2^1));
}.

Global Instance Impl_Integer_for_U8 : Integer.Trait U8.t := {
  Integer.to_Z (i : U8.t) :=
    let 'U8.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    U8.Make (i mod (2^8));
}.

Global Instance Impl_Integer_for_U16 : Integer.Trait U16.t := {
  Integer.to_Z (i : U16.t) :=
    let 'U16.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    U16.Make (i mod (2^16));
}.

Global Instance Impl_Integer_for_U32 : Integer.Trait U32.t := {
  Integer.to_Z (i : U32.t) :=
    let 'U32.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    U32.Make (i mod (2^32));
}.

Global Instance Impl_Integer_for_U64 : Integer.Trait U64.t := {
  Integer.to_Z (i : U64.t) :=
    let 'U64.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    U64.Make (i mod (2^64));
}.

Global Instance Impl_Integer_for_I1 : Integer.Trait I1.t := {
  Integer.to_Z (i : I1.t) :=
    let 'I1.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    I1.Make (((i + 2^0) mod (2^1)) - 2^0);
}.

Global Instance Impl_Integer_for_I8 : Integer.Trait I8.t := {
  Integer.to_Z (i : I8.t) :=
    let 'I8.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    I8.Make (((i + 2^7) mod (2^8)) - 2^7);
}.

Global Instance Impl_Integer_for_I16 : Integer.Trait I16.t := {
  Integer.to_Z (i : I16.t) :=
    let 'I16.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    I16.Make (((i + 2^15) mod (2^16)) - 2^15);
}.

Global Instance Impl_Integer_for_I32 : Integer.Trait I32.t := {
  Integer.to_Z (i : I32.t) :=
    let 'I32.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    I32.Make (((i + 2^31) mod (2^32)) - 2^31);
}.

Global Instance Impl_Integer_for_I64 : Integer.Trait I64.t := {
  Integer.to_Z (i : I64.t) :=
    let 'I64.Make i := i in
    i;
  Integer.of_Z (i : Z) :=
    I64.Make (((i + 2^63) mod (2^64)) - 2^63);
}.

Module Array.
  (** We keep the [size] explicit even if this is not needed as we represent things with a list. We
      use it as a marker to guide the type-classes inference mechanism as this is done in Noir. *)
  Inductive t (A : Set) (size : U32.t) : Set :=
  | Make (array : list A).
  Arguments Make {_ _}.

  Global Instance Impl_ToValue {A : Set} `{ToValue.Trait A} {size : U32.t} :
      ToValue.Trait (t A size) := {
    to_value (array : t A size) :=
      let 'Make array := array in
      Value.Array (List.map to_value array);
  }.

  Definition repeat {A : Set} (size : U32.t) (value : A) : t A size :=
    Make (List.repeat value (Z.to_nat (Integer.to_Z size))).
End Array.

Module Eq.
  Class Trait (Self : Set) : Set := {
    eq : Self -> Self -> bool;
  }.
End Eq.

Global Instance Impl_Eq_for_U8 : Eq.Trait U8.t := {
  Eq.eq (self other : U8.t) :=
    let 'U8.Make self := self in
    let 'U8.Make other := other in
    self =? other;
}.

Global Instance Impl_Eq_for_Array {A : Set} `{Eq.Trait A} {size : U32.t} :
    Eq.Trait (Array.t A size) := {
  Eq.eq (self other : Array.t A size) :=
    let 'Array.Make self := self in
    let 'Array.Make other := other in
    List.fold_left andb (List.zip Eq.eq self other) true;
}.
