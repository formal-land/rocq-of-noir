Require Export Coq.Strings.Ascii.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
From Ltac2 Require Ltac2.
Require Export RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

(* Activate the modulo arithmetic in [lia] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope char_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.
Global Open Scope bool_scope.

Export List.ListNotations.

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.
Arguments existS {_ _}.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module Ty.
  Module Signedness.
    Inductive t : Set :=
    | Signed
    | Unsigned.
  End Signedness.

  Module IntegerBitSize.
    Inductive t : Set :=
    | One
    | Eight
    | Sixteen
    | ThirtyTwo
    | SixtyFour.
  End IntegerBitSize.

  Inductive t : Set :=
  | Field
  | Integer (signedness : Signedness.t) (bit_size : IntegerBitSize.t).
End Ty.

Module Value.
  Inductive t : Set :=
  | Tt
  | Bool (b : bool)
  | Integer (integer : Z)
  | String (s : string)
  | FmtStr : string -> Z -> t -> t
  | Array (values : list t)
  | Slice (values : list t)
  | Tuple (values : list t)
  | Closure : {'(Value, M) : (Set * Set) @ list Value -> M} -> t.

  Parameter fmt_str : string -> Z -> t -> t.
End Value.

Module Primitive.
  Inductive t : Set :=
  | GetFunction (path : string) (id : Z).
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive (primitive : Primitive.t) (k : Value.t -> t A)
  | CallClosure (closure : Value.t) (args : list Value.t) (k : A -> t A)
  | Let (e : t A) (k : A -> t A)
  | Loop (body : t A) (k : A -> t A)
  | Impossible (message : string).
  Arguments Pure {_}.
  Arguments CallPrimitive {_}.
  Arguments CallClosure {_}.
  Arguments Let {_}.
  Arguments Loop {_}.
  Arguments Impossible {_}.

  Fixpoint let_ {A : Set} (e1 : t A) (e2 : A -> t A) : t A :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure f args k =>
      CallClosure f args (fun v => let_ (k v) e2)
    | Let e k =>
      Let e (fun v => let_ (k v) e2)
    | Loop body k =>
      Loop body (fun v => let_ (k v) e2)
    | Impossible message => Impossible message
    end.
End LowM.

Module Result.
  Inductive t : Set :=
  | Ok (value : Value.t)
  | Break
  | Continue
  | Panic {A : Set} (payload : A).
End Result.

Module M.
  Definition t : Set :=
    LowM.t Result.t.

  Definition pure (value : Value.t) : M.t :=
    LowM.Pure (Result.Ok value).

  Definition let_ (e1 : M.t) (e2 : Value.t -> M.t) : M.t :=
    LowM.let_ e1 (fun v1 =>
    match v1 with
    | Result.Ok v1 => e2 v1
    | _ => LowM.Pure v1
    end).

  Definition let_strong (e1 : M.t) (e2 : Value.t -> M.t) : M.t :=
    LowM.Let e1 (fun v1 =>
    match v1 with
    | Result.Ok v1 => e2 v1
    | _ => LowM.Pure v1
    end).

  (** This parameter is used as a marker to allow a monadic notation
      without naming all intermediate results. Computation represented using
      this markers can be translated to a regular monadic computation using
      [M.monadic] tactic. *)
  Parameter run : M.t -> Value.t.

  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v := ?x in @?f v] =>
      refine (let_strong _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (let_ _ _);
              [ monadic y
              | let w := fresh "v" in
                intro w;
                let z := context ctxt [w] in
                monadic z
              ]
          end
        ]
    | context ctxt [run ?x] =>
      lazymatch context ctxt [run x] with
      | run x => monadic x
      | _ =>
        refine (let_ _ _);
          [ monadic x
          | let v := fresh "v" in
            intro v;
            let y := context ctxt [v] in
            monadic y
          ]
      end
    | _ =>
      lazymatch type of e with
      | M.t => exact e
      | _ => exact (pure e)
      end
    end.

  Module Notations.
    Notation "'let-' a := b 'in' c" :=
      (LowM.let_ b (fun a => c))
        (at level 200, b at level 100, a name).

    Notation "'let*' a ':=' b 'in' c" :=
      (let_ b (fun a => c))
      (at level 200, a pattern, b at level 100, c at level 200).

    Notation "'let~' a := b 'in' c" :=
      (let_strong b (fun a => c))
        (at level 200, a pattern, b at level 100).

    Notation "'do~' a 'in' b" :=
      (let_strong a (fun _ => b))
      (at level 200).

    Notation "e (| e1 , .. , en |)" :=
      (run ((.. (e e1) ..) en))
      (at level 100).

    Notation "e (||)" :=
      (run e)
      (at level 100).

    Notation "[[ e ]]" :=
      (ltac:(M.monadic e))
      (only parsing).
  End Notations.
  Import Notations.

  Definition call_primitive (primitive : Primitive.t) : M.t :=
    LowM.CallPrimitive primitive pure.
  (* Make it transparent *)
  Arguments call_primitive /.

  Definition call_closure (closure : Value.t) (args : list Value.t) : M.t :=
    LowM.CallClosure closure args LowM.Pure.

  Definition impossible (message : string) : M.t :=
    LowM.Impossible message.

  Definition get_function (path : string) (id : Z) : M.t :=
    call_primitive (Primitive.GetFunction path id).

  Definition assert (condition : Value.t) (message : option Value.t) : M.t :=
    match condition with
    | Value.Bool b =>
      if b then
        pure Value.Tt
      else
        LowM.Pure (Result.Panic message)
    | _ => LowM.Impossible "assert: expected a boolean"
    end.

  Parameter cast : Value.t -> Ty.t -> M.t.

  Parameter index : Value.t -> Value.t -> M.t.

  Parameter assign : Value.t -> Value.t -> M.t.

  Parameter extract_tuple_field : Value.t -> Z -> M.t.

  Definition if_ (condition : Value.t) (then_ : M.t) (else_ : option M.t) : M.t :=
    match condition with
    | Value.Bool true => then_
    | Value.Bool false =>
      match else_ with
      | Some else_ => else_
      | None => pure Value.Tt
      end
    | _ => LowM.Impossible "if: expected a boolean"
    end.

  Parameter for_ : Value.t -> Value.t -> (Value.t -> M.t) -> M.t.
End M.

Export M.Notations.

Module Builtin.
  Parameter __to_be_radix : Value.t.

  Parameter as_bytes : Value.t.

  Parameter assert_constant : Value.t.

  Parameter is_unconstrained : Value.t.

  Parameter len : Value.t.
End Builtin.

(*
pub enum UnaryOp {
    Minus,
    Not,
    MutableReference,
    Dereference {
        implicitly_added: bool,
    },
}
*)
Module Unary.
  Parameter minus : Value.t -> M.t.

  Parameter not : Value.t -> M.t.

  Parameter mutable_reference : Value.t -> M.t.

  Parameter dereference : Value.t -> M.t.
End Unary.

(*
pub enum BinaryOpKind {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    And,
    Or,
    Xor,
    ShiftRight,
    ShiftLeft,
    Modulo,
}
*)
Module Binary.
  Parameter add : Value.t -> Value.t -> M.t.

  Parameter subtract : Value.t -> Value.t -> M.t.

  Parameter multiply : Value.t -> Value.t -> M.t.

  Parameter divide : Value.t -> Value.t -> M.t.

  Parameter equal : Value.t -> Value.t -> M.t.

  Parameter not_equal : Value.t -> Value.t -> M.t.

  Parameter less : Value.t -> Value.t -> M.t.

  Parameter less_equal : Value.t -> Value.t -> M.t.

  Parameter greater : Value.t -> Value.t -> M.t.

  Parameter greater_equal : Value.t -> Value.t -> M.t.

  Parameter and_ : Value.t -> Value.t -> M.t.

  Parameter or_ : Value.t -> Value.t -> M.t.

  Parameter xor : Value.t -> Value.t -> M.t.

  Parameter shift_right : Value.t -> Value.t -> M.t.

  Parameter shift_left : Value.t -> Value.t -> M.t.

  Parameter modulo : Value.t -> Value.t -> M.t.
End Binary.
