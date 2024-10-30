Require Import CoqOfNoir.CoqOfNoir.

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
  Reserved Notation "{{ p , state_in | e ⇓ output | state_out }}".

  Inductive t {State Address : Set} `{State.Trait State Address}
      (p : Z) (output : Result.t) (state_out : State) :
      State -> M.t -> Prop :=
  | Pure :
    (* This should be the only case where the input and output states are the same. *)
    {{ p, state_out | LowM.Pure output ⇓ output | state_out }}
  | CallPrimitiveStateAlloc
      (value : Value.t)
      (address : Address)
      (k : Value.t -> M.t)
      (state_in state_in' : State) :
    let pointer := Pointer.Mutable (Pointer.Mutable.Make address []) in
    State.alloc_write address state_in value = Some state_in' ->
    {{ p, state_in' | k (Value.Pointer pointer) ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.StateAlloc value) k ⇓ output | state_out }}
  | CallPrimitiveStateRead
      (address : Address)
      (value : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    State.read address state_in = Some value ->
    {{ p, state_in | k value ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.StateRead address) k ⇓ output | state_out }}
  | CallPrimitiveStateWrite
      (value : Value.t)
      (address : Address)
      (k : unit -> M.t)
      (state_in state_in' : State) :
    State.alloc_write address state_in value = Some state_in' ->
    {{ p, state_in' | k tt ⇓ output | state_out }} ->
    {{ p, state_in |
      LowM.CallPrimitive (Primitive.StateWrite address value) k ⇓ output
    | state_out }}
  | CallPrimitiveGetFieldPrime
      (k : Z -> M.t)
      (state_in : State) :
    {{ p, state_in | k p ⇓ output | state_out }} ->
    {{ p, state_in |
      LowM.CallPrimitive Primitive.GetFieldPrime k ⇓ output
    | state_out }}
  | CallPrimitiveIsEqualTrue
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    (* The hypothesis of equality is explicit as this should be more convenient for the proofs *)
    value1 = value2 ->
    {{ p, state_in | k true ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  | CallPrimitiveIsEqualFalse
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    value1 <> value2 ->
    {{ p, state_in | k false ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallPrimitive (Primitive.IsEqual value1 value2) k ⇓ output | state_out }}
  (*| CallPrimitiveGetFunction
      (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (function : PolymorphicFunction.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    let closure := Value.Closure (existS (_, _) (function generic_consts generic_tys)) in
    M.IsFunction name function ->
    {{ p, state_in | k closure ⇓ output | state_out }} ->
    {{ p, state_in |
      LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output
    | state_out }}
  | CallClosure
      (output_inter : Value.t + Exception.t)
      (f : list Value.t -> M.t) (args : list Value.t)
      (k : Value.t + Exception.t -> M.t)
      (state_in state_inter : State) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ p, state_in | f args ⇓ output_inter | state_inter }} ->
    (* We do not de-allocate what was already there on the state. *)
    (* IsWritePreserved.t state state' -> *)
    {{ p, state_inter | k output_inter ⇓ output | state_out }} ->
    {{ p, state_in | LowM.CallClosure closure args k ⇓ output | state_out }}
  *)
  | Let
      (e : M.t)
      (k : Result.t -> M.t)
      (output_inter : Result.t)
      (state_in state_inter : State) :
    {{ p, state_in | e ⇓ output_inter | state_inter }} ->
    {{ p, state_inter | k output_inter ⇓ output | state_out }} ->
    {{ p, state_in | LowM.Let e k ⇓ output | state_out }}

  where "{{ p , state_in | e ⇓ output | state_out }}" :=
    (t p output state_out state_in e).
End Run.
