Require Export Coq.Strings.Ascii.
Require Coq.Strings.HexString.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require coqutil.Datatypes.List.
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

Module Pointer.
  Module Index.
    Inductive t : Set :=
    | Field (index : Z)
    | Index (index : Z).
  End Index.

  Module Path.
    Definition t : Set :=
      list Index.t.
  End Path.

  Module Mutable.
    Inductive t : Set :=
    | Make {Address : Set} (address : Address) (path : Path.t).
  End Mutable.

  Inductive t (Value : Set) : Set :=
  | Immediate (value : Value)
  | Mutable (mutable : Mutable.t).
  Arguments Immediate {_}.
  Arguments Mutable {_}.
End Pointer.

Module Value.
  Inductive t : Set :=
  | Bool (b : bool)
  | Integer (integer : Z)
  | String (s : string)
  | FmtStr : string -> Z -> t -> t
  | Pointer (pointer : Pointer.t t)
  | Array (values : list t)
  | Slice (values : list t)
  | Tuple (values : list t)
  | Closure : {'(Value, M) : (Set * Set) @ list Value -> M} -> t.

  Parameter fmt_str : string -> Z -> t -> t.

  (** Read the value at an index in a value. Useful to read sub-pointers. *)
  Definition read_index (value : t) (index : Pointer.Index.t) : option Value.t :=
    match index with
    | Pointer.Index.Field i =>
      match value with
      | Tuple values => List.nth_error values (Z.to_nat i)
      | _ => None
      end
    | Pointer.Index.Index i =>
      match value with
      | Array values => List.nth_error values (Z.to_nat i)
      | _ => None
      end
    end.

  Fixpoint read_path (value : t) (path : Pointer.Path.t) : option Value.t :=
    match path with
    | [] => Some value
    | index :: sub_path =>
      let sub_value := read_index value index in
      match sub_value with
      | Some sub_value => read_path sub_value sub_path
      | None => None
      end
    end.

  Definition write_index (value : t) (index : Pointer.Index.t) (update : Value.t) :
      option Value.t :=
    match index with
    | Pointer.Index.Field i =>
      match value with
      | Tuple values =>
        match List.listUpdate_error values (Z.to_nat i) update with
        | Some new_values => Some (Tuple values)
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.Index i =>
      match value with
      | Array values =>
        match List.listUpdate_error values (Z.to_nat i) update with
        | Some new_values => Some (Array values)
        | None => None
        end
      | _ => None
      end
    end.

  Fixpoint write_path (value : t) (path : Pointer.Path.t) (update : Value.t) : option Value.t :=
    match path with
    | [] => Some update
    | index :: sub_path =>
      let sub_value := read_index value index in
      match sub_value with
      | Some sub_value =>
        match write_path sub_value sub_path update with
        | Some new_sub_value => write_index value index new_sub_value
        | None => None
        end
      | None => None
      end
    end.
End Value.

Module Primitive.
  Inductive t : Set :=
  | StateAlloc (value : Value.t)
  | StateRead {Address : Set} (address : Address)
  | StateWrite {Address : Set} (address : Address) (value : Value.t)
  | GetFunction (path : string) (id : Z)
  | IsEqual (value1 value2 : Value.t).
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
      (* (M.pure e) *)
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

  Definition alloc (value : Value.t) : Value.t :=
    Value.Pointer (Pointer.Immediate value).
  Arguments alloc /.

  Definition alloc_mutable (value : Value.t) : M.t :=
    call_primitive (Primitive.StateAlloc value).
  Arguments alloc_mutable /.

  Definition read (r : Value.t) : M.t :=
    match r with
    | Value.Pointer pointer =>
      match pointer with
      | Pointer.Immediate value => pure value
      | Pointer.Mutable (Pointer.Mutable.Make address path) =>
        let* value := call_primitive (Primitive.StateRead address) in
        match Value.read_path value path with
        | Some sub_value => pure sub_value
        | None => impossible "read: invalid sub-pointer"
        end
      end
    | _ => impossible "read: expected a pointer"
    end.
  Arguments read /.

  Definition write (r update : Value.t) : M.t :=
    match r with
    | Value.Pointer (Pointer.Mutable (Pointer.Mutable.Make address path)) =>
      let* value := call_primitive (Primitive.StateRead address) in
      match Value.write_path value path update with
      | Some new_value => call_primitive (Primitive.StateWrite address new_value)
      | None => impossible "write: invalid sub_pointer"
      end
    | _ => impossible "write: expected a mutable pointer"
    end.
  Arguments write /.

  Definition copy (r : Value.t) : M.t :=
    let* v := read r in
    pure (alloc v).
  Arguments copy /.

  Definition copy_mutable (r : Value.t) : M.t :=
    let* v := read r in
    alloc_mutable v.
  Arguments copy /.

  Definition get_function (path : string) (id : Z) : M.t :=
    call_primitive (Primitive.GetFunction path id).

  Definition assert (condition : Value.t) (message : option Value.t) : M.t :=
    match condition with
    | Value.Bool b =>
      if b then
        pure (Value.Tuple [])
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
      | None => pure (Value.Tuple [])
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

  Definition equal (value1 value2 : Value.t) : M.t :=
    M.call_primitive (Primitive.IsEqual value1 value2).

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

Module State.
  Class Trait (State Address : Set) : Type := {
    read (a : Address) : State -> option Value.t;
    alloc_write (a : Address) : State -> Value.t -> option State;
  }.
 
  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (a : Address) (s : State) (v : Value.t) :
        match alloc_write a s v with
        | Some _ => True
        | None => read a s = None
        end;
      same (a : Address) (s : State) (v : Value.t) :
        match alloc_write a s v with
        | Some s => read a s = Some v
        | None => True
        end;
      different (a1 a2 : Address) (s : State) (v2 : Value.t) :
        a1 <> a2 ->
        match alloc_write a2 s v2 with
        | Some s' => read a1 s' = read a1 s
        | None => True
        end;
        }.
  End Valid.
End State.

Module Run.
  Reserved Notation "{{ state_in | e ⇓ output | state_out }}".

  Inductive t {State Address : Set} `{State.Trait State Address}
      (output : Result.t) (state_out : State) :
      State -> M.t -> Prop :=
  | Pure :
    (* This should be the only case where the input and output states are the same. *)
    {{ state_out | LowM.Pure output ⇓ output | state_out }}
  | CallPrimitiveStateAlloc
      (value : Value.t)
      (address : Address)
      (k : Value.t -> M.t)
      (state_in state_in' : State) :
    let pointer := Pointer.Mutable (Pointer.Mutable.Make address []) in
    State.alloc_write address state_in value = Some state_in' ->
    {{ state_in' | k (Value.Pointer pointer) ⇓ output | state_out }} ->
    {{ state_in | LowM.CallPrimitive (Primitive.StateAlloc value) k ⇓ output | state_out }}
  | CallPrimitiveStateRead
      (address : Address)
      (value : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    State.read address state_in = Some value ->
    {{ state_in | k value ⇓ output | state_out }} ->
    {{ state_in | LowM.CallPrimitive (Primitive.StateRead address) k ⇓ output | state_out }}
  | CallPrimitiveStateWrite
      (value : Value.t)
      (address : Address)
      (k : Value.t -> M.t)
      (state_in state_in' : State) :
    State.alloc_write address state_in value = Some state_in' ->
    {{ state_in' | k (Value.Tuple []) ⇓ output | state_out }} ->
    {{ state_in | LowM.CallPrimitive (Primitive.StateWrite address value) k ⇓ output | state_out }}
  | CallPrimitiveIsEqualTrue
      (value1 value2 : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    (* The hypothesis of equality is explicit as this should be more convenient for the proofs *)
    value1 = value2 ->
    {{ state_in | k (Value.Bool true) ⇓ output | state_out }} ->
    {{ state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  | CallPrimitiveIsEqualFalse
      (value1 value2 : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    value1 <> value2 ->
    {{ state_in | k (Value.Bool false) ⇓ output | state_out }} ->
    {{ state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  (*| CallPrimitiveGetFunction
      (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (function : PolymorphicFunction.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    let closure := Value.Closure (existS (_, _) (function generic_consts generic_tys)) in
    M.IsFunction name function ->
    {{ state_in | k closure ⇓ output | state_out }} ->
    {{ state_in |
      LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output
    | state_out }}
  | CallClosure
      (output_inter : Value.t + Exception.t)
      (f : list Value.t -> M.t) (args : list Value.t)
      (k : Value.t + Exception.t -> M.t)
      (state_in state_inter : State) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ state_in | f args ⇓ output_inter | state_inter }} ->
    (* We do not de-allocate what was already there on the state. *)
    (* IsWritePreserved.t state state' -> *)
    {{ state_inter | k output_inter ⇓ output | state_out }} ->
    {{ state_in | LowM.CallClosure closure args k ⇓ output | state_out }}
  *)
  | Let
      (e : M.t)
      (k : Result.t -> M.t)
      (output_inter : Result.t)
      (state_in state_inter : State) :
    {{ state_in | e ⇓ output_inter | state_inter }} ->
    {{ state_inter | k output_inter ⇓ output | state_out }} ->
    {{ state_in | LowM.Let e k ⇓ output | state_out }}

  where "{{ state_in | e ⇓ output | state_out }}" :=
    (t output state_out state_in e).
End Run.
