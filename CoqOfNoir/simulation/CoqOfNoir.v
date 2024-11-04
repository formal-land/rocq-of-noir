Require Import CoqOfNoir.CoqOfNoir.

Module Panic.
  Inductive t (A : Set) : Set :=
  | Value : A -> t A
  (** The [Panic] works with an existential type, so we can return any payload for errors. This is
      useful for debugging. Then we cannot catch the error and compute with it as we do not know the
      type anymore, but catching panic errors is not supposed to happen in Rust. *)
  | Panic (payload : {Error : Set @ Error}) : t A.
  Arguments Value {_}.
  Arguments Panic {_}.

  Definition return_ {A : Set} (value : A) : t A :=
    Value value.

  Definition panic {A Error : Set} (error : Error) : t A :=
    Panic (existS _ error).

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Value value => f value
    | Panic error => Panic error
    end.

  Definition fold_left {A B : Set} (init : A) (l : list B) (f : A -> B -> t A) : t A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition map {A B : Set} (l : list A) (f : A -> t B) : t (list B) :=
    List.fold_right
      (fun x acc => bind acc (fun acc => bind (f x) (fun x => return_ (x :: acc))))
      (return_ []) l.
End Panic.

Module PanicNotations.
  Notation "M!" := Panic.t.

  Notation "return!" := Panic.return_.
  Notation "panic!" := Panic.panic.

  Notation "'let!' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'do!' X 'in' Y" :=
    (Panic.bind X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).

  Notation "fold!" := Panic.fold_left.

  Notation "map!" := Panic.map.
End PanicNotations.

Export PanicNotations.

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

Module SemiInteger.
  Class Trait (Self : Set) : Set := {
    to_Z : Self -> Z;
  }.
End SemiInteger.

Global Instance Impl_SemiInteger_for_Field : SemiInteger.Trait Field.t := {
  SemiInteger.to_Z (i : Field.t) :=
    let 'Field.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_U1 : SemiInteger.Trait U1.t := {
  SemiInteger.to_Z (i : U1.t) :=
    let 'U1.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_U8 : SemiInteger.Trait U8.t := {
  SemiInteger.to_Z (i : U8.t) :=
    let 'U8.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_U16 : SemiInteger.Trait U16.t := {
  SemiInteger.to_Z (i : U16.t) :=
    let 'U16.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_U32 : SemiInteger.Trait U32.t := {
  SemiInteger.to_Z (i : U32.t) :=
    let 'U32.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_U64 : SemiInteger.Trait U64.t := {
  SemiInteger.to_Z (i : U64.t) :=
    let 'U64.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_I1 : SemiInteger.Trait I1.t := {
  SemiInteger.to_Z (i : I1.t) :=
    let 'I1.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_I8 : SemiInteger.Trait I8.t := {
  SemiInteger.to_Z (i : I8.t) :=
    let 'I8.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_I16 : SemiInteger.Trait I16.t := {
  SemiInteger.to_Z (i : I16.t) :=
    let 'I16.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_I32 : SemiInteger.Trait I32.t := {
  SemiInteger.to_Z (i : I32.t) :=
    let 'I32.Make i := i in
    i;
}.

Global Instance Impl_SemiInteger_for_I64 : SemiInteger.Trait I64.t := {
  SemiInteger.to_Z (i : I64.t) :=
    let 'I64.Make i := i in
    i;
}.

Module Integer.
  Class Trait (Self : Set) `{SemiInteger.Trait Self} : Set := {
    of_Z : Z -> Self;
  }.

  Definition to_Z {Self : Set} `{Trait Self} (self : Self) : Z :=
    SemiInteger.to_Z self.

  Definition to_nat {Self : Set} `{Trait Self} (self : Self) : nat :=
    Z.to_nat (to_Z self).

  Definition add {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (SemiInteger.to_Z self + SemiInteger.to_Z other).

  Definition sub {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (SemiInteger.to_Z self - SemiInteger.to_Z other).

  Definition mul {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (SemiInteger.to_Z self * SemiInteger.to_Z other).

  Definition div {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (SemiInteger.to_Z self / SemiInteger.to_Z other).

  Definition mod_ {Self : Set} `{Trait Self} (self other : Self) : Self :=
    of_Z (SemiInteger.to_Z self mod SemiInteger.to_Z other).

  Definition of_bool {Self : Set} `{Trait Self} (b : bool) : Self :=
    of_Z (if b then 1 else 0).
End Integer.

Global Instance Impl_Integer_for_U1 : Integer.Trait U1.t := {
  Integer.of_Z (i : Z) :=
    U1.Make (i mod (2^1));
}.

Global Instance Impl_Integer_for_U8 : Integer.Trait U8.t := {
  Integer.of_Z (i : Z) :=
    U8.Make (i mod (2^8));
}.

Global Instance Impl_Integer_for_U16 : Integer.Trait U16.t := {
  Integer.of_Z (i : Z) :=
    U16.Make (i mod (2^16));
}.

Global Instance Impl_Integer_for_U32 : Integer.Trait U32.t := {
  Integer.of_Z (i : Z) :=
    U32.Make (i mod (2^32));
}.

Global Instance Impl_Integer_for_U64 : Integer.Trait U64.t := {
  Integer.of_Z (i : Z) :=
    U64.Make (i mod (2^64));
}.

Global Instance Impl_Integer_for_I1 : Integer.Trait I1.t := {
  Integer.of_Z (i : Z) :=
    I1.Make (((i + 2^0) mod (2^1)) - 2^0);
}.

Global Instance Impl_Integer_for_I8 : Integer.Trait I8.t := {
  Integer.of_Z (i : Z) :=
    I8.Make (((i + 2^7) mod (2^8)) - 2^7);
}.

Global Instance Impl_Integer_for_I16 : Integer.Trait I16.t := {
  Integer.of_Z (i : Z) :=
    I16.Make (((i + 2^15) mod (2^16)) - 2^15);
}.

Global Instance Impl_Integer_for_I32 : Integer.Trait I32.t := {
  Integer.of_Z (i : Z) :=
    I32.Make (((i + 2^31) mod (2^32)) - 2^31);
}.

Global Instance Impl_Integer_for_I64 : Integer.Trait I64.t := {
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
    Make (List.repeat value (Z.to_nat (SemiInteger.to_Z size))).

  Definition get {A Index: Set} `{SemiInteger.Trait Index} {size : U32.t}
      (array : t A size) (index : Index) :
      M! A :=
    let 'Make array := array in
    match List.nth_error array (Z.to_nat (SemiInteger.to_Z index)) with
    | Some result => return! result
    | None => panic! ("Array.get: index out of bounds", array, index)
    end.
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
