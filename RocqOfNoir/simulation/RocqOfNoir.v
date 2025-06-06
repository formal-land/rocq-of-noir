Require Import RocqOfNoir.RocqOfNoir.

Class ToValue (Self : Set) : Set := {
  to_value : Self -> Value.t;
}.

Module Panic.
  Definition t (A : Set) : Set :=
    option A.

  Definition return_ {A : Set} (value : A) : t A :=
    Some value.
  Arguments return_ /.

  Definition panic {A E : Set} (error : E) : t A :=
    None.
  (* So that the error payload appears for debugging *)
  Opaque panic.

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Some value => f value
    | None => None
    end.

  Definition fold_left {A B : Set} (init : A) (l : list B) (f : A -> B -> t A) : t A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition assert (condition : bool) : t unit :=
    if condition then
      return_ tt
    else
      panic "assert failure".
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
End PanicNotations.
Export PanicNotations.

Module Unit.
  Global Instance IsToValue : ToValue unit := {
    to_value (_ : unit) :=
      Value.Tuple [];
  }.

  Lemma rewrite_to_value :
    Value.Tuple [] = to_value tt.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End Unit.

Module Bool.
  Global Instance IsToValue : ToValue bool := {
    to_value (b : bool) :=
      Value.Bool b;
  }.

  Lemma rewrite_to_value :
    Value.Bool = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.
End Bool.

Module Integer.
  Record t {kind : IntegerKind.t} : Set := {
    value : Z;
  }.
  Arguments t : clear implicits.

  Global Instance IsToValue (kind : IntegerKind.t) : ToValue (Integer.t kind) := {
    to_value (i : Integer.t kind) :=
      Value.Integer kind i.(value);
  }.

  Lemma rewrite_to_value (kind : IntegerKind.t) :
    (fun (i : t kind) => Value.Integer kind i.(value)) = to_value.
  Proof. reflexivity. Qed.
  Global Hint Rewrite rewrite_to_value : to_value.

  Definition cast {from : IntegerKind.t} (i : t from) (to : IntegerKind.t) : M! (t to) :=
    let i := i.(value) in
    match to with
    | IntegerKind.U1 =>
      if (0 <=? i) && (i <? 2) then
        return! ({| value := i |} : t IntegerKind.U1)
      else
        panic! ("cast: out of bounds", i, from, to)
    | IntegerKind.U8 =>
      if (0 <=? i) && (i <? 2^8) then
        return! ({| value := i |} : t IntegerKind.U8)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.U16 =>
      if (0 <=? i) && (i <? 2^16) then
        return! ({| value := i |} : t IntegerKind.U16)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.U32 =>
      if (0 <=? i) && (i <? 2^32) then
        return! ({| value := i |} : t IntegerKind.U32)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.U64 =>
      if (0 <=? i) && (i <? 2^64) then
        return! ({| value := i |} : t IntegerKind.U64)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.I1 =>
      if (-(2^0) <=? i) && (i <? 2^0) then
        return! ({| value := i |} : t IntegerKind.I1)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.I8 =>
      if (-(2^7) <=? i) && (i <? 2^7) then
        return! ({| value := i |} : t IntegerKind.I8)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.I16 =>
      if (-(2^15) <=? i) && (i <? 2^15) then
        return! ({| value := i |} : t IntegerKind.I16)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.I32 =>
      if (-(2^31) <=? i) && (i <? 2^31) then
        return! ({| value := i |} : t IntegerKind.I32)
      else
        panic! ("cast: out of bounds", i, to)
    | IntegerKind.I64 =>
      if (-(2^63) <=? i) && (i <? 2^63) then
        return! ({| value := i |} : t IntegerKind.I64)
      else
        panic! ("cast: out of bounds", i, to)
    end.
End Integer.

Module Field.
  Record t : Set := {
    value : Z;
  }.

  Global Instance IsToValue : ToValue t := {
    to_value (f : t) :=
      Value.Field f.(value);
  }.

  Definition add (p : Z) (x y : t) : t :=
    {| Field.value := (x.(Field.value) + y.(Field.value)) mod p |}.

  Definition sub (p : Z) (x y : t) : t :=
    {| Field.value := (x.(Field.value) - y.(Field.value)) mod p |}.

  Definition mul (p : Z) (x y : t) : t :=
    {| Field.value := (x.(Field.value) * y.(Field.value)) mod p |}.

  Definition div (p : Z) (x y : t) : t :=
    {| Field.value := (x.(Field.value) / y.(Field.value)) mod p |}.

  Definition cast {from : IntegerKind.t} (p : Z) (x : Integer.t from) : M! t :=
    let x := x.(Integer.value) in
    if (0 <=? x) && (x <? p) then
      return! {| Field.value := x |}
    else
      panic! ("cast: out of bounds", x, from, p).
End Field.

Module U1.
  Definition t : Set := Integer.t IntegerKind.U1.
End U1.

Module U8.
  Definition t : Set := Integer.t IntegerKind.U8.
End U8.

Module U16.
  Definition t : Set := Integer.t IntegerKind.U16.
End U16.

Module U32.
  Definition t : Set := Integer.t IntegerKind.U32.
End U32.

Module U64.
  Definition t : Set := Integer.t IntegerKind.U64.
End U64.

Module I1.
  Definition t : Set := Integer.t IntegerKind.I1.
End I1.

Module I8.
  Definition t : Set := Integer.t IntegerKind.I8.
End I8.

Module I16.
  Definition t : Set := Integer.t IntegerKind.I16.
End I16.

Module I32.
  Definition t : Set := Integer.t IntegerKind.I32.
End I32.

Module I64.
  Definition t : Set := Integer.t IntegerKind.I64.
End I64.

Module BinaryInteger.
  Class C (Self : Set) : Set := {
    to_Z : Self -> Z;
    of_Z : Z -> Self;
    min : Z;
    max : Z;
  }.

  Definition add {Self : Set} `{C Self} (self other : Self) : Self :=
    of_Z (to_Z self + to_Z other).

  Definition sub {Self : Set} `{C Self} (self other : Self) : Self :=
    of_Z (to_Z self - to_Z other).

  Definition mul {Self : Set} `{C Self} (self other : Self) : Self :=
    of_Z (to_Z self * to_Z other).

  Definition div {Self : Set} `{C Self} (self other : Self) : Self :=
    of_Z (to_Z self / to_Z other).

  Definition mod_ {Self : Set} `{C Self} (self other : Self) : Self :=
    of_Z (to_Z self mod to_Z other).

  Definition of_bool {Self : Set} `{C Self} (b : bool) : Self :=
    of_Z (if b then 1 else 0).
End BinaryInteger.

Global Instance Impl_Integer_for_U1 : BinaryInteger.C U1.t := {
  Integer.to_Z (i : U1.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := i mod (2^1) |};
  Integer.min := 0;
  Integer.max := 1;
}.

Global Instance Impl_Integer_for_U8 : BinaryInteger.C U8.t := {
  Integer.to_Z (i : U8.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := i mod (2^8) |};
  Integer.min := 0;
  Integer.max := 2^8 - 1;
}.

Global Instance Impl_Integer_for_U16 : BinaryInteger.C U16.t := {
  Integer.to_Z (i : U16.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := i mod (2^16) |};
  Integer.min := 0;
  Integer.max := 2^16 - 1;
}.

Global Instance Impl_Integer_for_U32 : BinaryInteger.C U32.t := {
  Integer.to_Z (i : U32.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := i mod (2^32) |};
  Integer.min := 0;
  Integer.max := 2^32 - 1;
}.

Global Instance Impl_Integer_for_U64 : BinaryInteger.C U64.t := {
  Integer.to_Z (i : U64.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := i mod (2^64) |};
  Integer.min := 0;
  Integer.max := 2^64 - 1;
}.

Global Instance Impl_Integer_for_I1 : BinaryInteger.C I1.t := {
  Integer.to_Z (i : I1.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := (((i + 2^0) mod (2^1)) - 2^0) |};
  Integer.min := -1;
  Integer.max := 0;
}.

Global Instance Impl_Integer_for_I8 : BinaryInteger.C I8.t := {
  Integer.to_Z (i : I8.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := (((i + 2^7) mod (2^8)) - 2^7) |};
  Integer.min := -2^7;
  Integer.max := 2^7 - 1;
}.

Global Instance Impl_Integer_for_I16 : BinaryInteger.C I16.t := {
  Integer.to_Z (i : I16.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := (((i + 2^15) mod (2^16)) - 2^15) |};
  Integer.min := -2^15;
  Integer.max := 2^15 - 1;
}.

Global Instance Impl_Integer_for_I32 : BinaryInteger.C I32.t := {
  Integer.to_Z (i : I32.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := (((i + 2^31) mod (2^32)) - 2^31) |};
  Integer.min := -2^31;
  Integer.max := 2^31 - 1;
}.

Global Instance Impl_Integer_for_I64 : BinaryInteger.C I64.t := {
  Integer.to_Z (i : I64.t) :=
    i.(Integer.value);
  Integer.of_Z (i : Z) :=
    {| Integer.value := (((i + 2^63) mod (2^64)) - 2^63) |};
  Integer.min := -2^63;
  Integer.max := 2^63 - 1;
}.

Module Array.
  (** We keep the [size] explicit even if this is not needed as we represent things with a list. We
      use it as a marker to guide the type-classes inference mechanism as this is done in Noir. *)
  Record t {A : Set} {size : U32.t} : Set := {
    value : list A;
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_ _}.

  Global Instance Impl_ToValue {A : Set} `{ToValue A} {size : U32.t} :
      ToValue (t A size) := {
    to_value (array : t A size) :=
      Value.Array (List.map to_value array.(value));
  }.

  Lemma rewrite_to_value {A : Set} `{ToValue A} {size : U32.t} (array : t A size) :
    Value.Array (List.map to_value array.(value)) = to_value array.
  Proof. reflexivity. Qed.
  Global Hint Rewrite @rewrite_to_value : to_value.

  Definition repeat {A : Set} (size : U32.t) (value : A) : t A size :=
    {|
      value := List.repeat value (Z.to_nat size.(Integer.value))
    |}.

  Definition read {A : Set} {size : U32.t} (array : t A size) (index : Z) : M! A :=
    match List.nth_error array.(value) (Z.to_nat index) with
    | Some result => return! result
    | None => panic! ("Array.get: index out of bounds", array, index)
    end.

  Definition write {A : Set} {size : U32.t} (array : t A size) (index : Z) (update : A) :
      M! (t A size) :=
    match List.listUpdate_error array.(value) (Z.to_nat index) update with
    | Some array => return! (Build_t array)
    | None => panic! ("Array.write: index out of bounds", array, index)
    end.
End Array.

Module Eq.
  Class Trait (Self : Set) : Set := {
    eq : Self -> Self -> bool;
  }.
End Eq.

Global Instance Impl_Eq_for_Integer (kind : IntegerKind.t) : Eq.Trait (Integer.t kind) := {
  Eq.eq (self other : Integer.t kind) :=
    self.(Integer.value) =? other.(Integer.value);
}.

Global Instance Impl_Eq_for_Array {A : Set} `{Eq.Trait A} {size : U32.t} :
    Eq.Trait (Array.t A size) := {
  Eq.eq (self other : Array.t A size) :=
    List.fold_left andb (List.zip Eq.eq self.(Array.value) other.(Array.value)) true;
}.

Definition cast_to_integer {kind_source : IntegerKind.t} {Target : Set} `{BinaryInteger.C Target}
    (value : Integer.t kind_source) :
    M! Target :=
  let value := value.(Integer.value) in
  if (BinaryInteger.min <=? value) && (value <=? BinaryInteger.max) then
    return! (BinaryInteger.of_Z value)
  else
    panic! ("cast: out of bounds", value).

Definition cast_to_field {kind : IntegerKind.t} (p : Z) (value : Integer.t kind) : M! Field.t :=
  let value := value.(Integer.value) in
  if (0 <=? value) && (value <? p) then
    return! {| Field.value := value |}
  else
    panic! ("cast: out of bounds", value).
