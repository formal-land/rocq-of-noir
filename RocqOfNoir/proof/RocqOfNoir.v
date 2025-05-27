Require Import RocqOfNoir.RocqOfNoir.
Require Import RocqOfNoir.simulation.RocqOfNoir.


Module State.
  Class Trait (State Address : Set) : Type := {
    read : State -> Address -> option Value.t;
    alloc_write : State -> Address -> Value.t -> option State;
  }.
 
  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (state : State) (address : Address) (value : Value.t) :
        match alloc_write state address value with
        | Some _ => True
        | None => read state address = None
        end;
      same (state : State) (address : Address) (value : Value.t) :
        match alloc_write state address value with
        | Some state => read state address = Some value
        | None => True
        end;
      different (state : State) (address1 address2 : Address) (value2 : Value.t) :
        address1 <> address2 ->
        match alloc_write state address2 value2 with
        | Some state' => read state' address1 = read state address1
        | None => True
        end;
        }.
  End Valid.
End State.
 
Module Run.
  Reserved Notation "{{ p , state_in ⏩ e 🔽 output }}".

  Inductive t {State Address : Set} `{State.Trait State Address}
      (p : Z) (output : option (Value.t * State)) :
      State -> M.t -> Prop :=
  | Pure
      (value : Value.t)
      (state_in : State) :
    output = Some (value, state_in) ->
    {{ p, state_in ⏩ M.Pure value 🔽 output }}
  | Panic (state_in : State) :
    output = None ->
    {{ p, state_in ⏩ M.Panic 🔽 output }}
  | CallPrimitiveStateAlloc
      (value : Value.t)
      (address : Address)
      (k : Value.t -> M.t)
      (state_in state_in' : State) :
    let pointer := Pointer.Mutable (Pointer.Mutable.Make address []) in
    State.read state_in address = None ->
    State.alloc_write state_in address value = Some state_in' ->
    {{ p, state_in' ⏩ k (Value.Pointer pointer) 🔽 output }} ->
    {{ p, state_in ⏩ M.CallPrimitive (Primitive.StateAlloc value) k 🔽 output }}
  | CallPrimitiveStateRead
      (address : Address)
      (value : Value.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    State.read state_in address = Some value ->
    {{ p, state_in ⏩ k value 🔽 output }} ->
    {{ p, state_in ⏩ M.CallPrimitive (Primitive.StateRead address) k 🔽 output }}
  | CallPrimitiveStateWrite
      (value : Value.t)
      (address : Address)
      (k : unit -> M.t)
      (state_in state_in' : State) :
    State.alloc_write state_in address value = Some state_in' ->
    {{ p, state_in' ⏩ k tt 🔽 output }} ->
    {{ p, state_in ⏩
      M.CallPrimitive (Primitive.StateWrite address value) k 🔽
      output
    }}
  | CallPrimitiveGetFieldPrime
      (k : Z -> M.t)
      (state_in : State) :
    {{ p, state_in ⏩ k p 🔽 output }} ->
    {{ p, state_in ⏩
      M.CallPrimitive Primitive.GetFieldPrime k 🔽
      output
    }}
  | CallPrimitiveIsEqualTrue
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    (* The hypothesis of equality is explicit as this should be more convenient for the proofs *)
    value1 = value2 ->
    {{ p, state_in ⏩ k true 🔽 output }} ->
    {{ p, state_in ⏩ M.CallPrimitive (Primitive.IsEqual value1 value2) k 🔽 output }}
  | CallPrimitiveIsEqualFalse
      (value1 value2 : Value.t)
      (k : bool -> M.t)
      (state_in : State) :
    value1 <> value2 ->
    {{ p, state_in ⏩ k false 🔽 output }} ->
    {{ p, state_in ⏩ M.CallPrimitive (Primitive.IsEqual value1 value2) k 🔽 output }}
  (* | CallClosure
      (f : list Value.t -> M.t) (args : list Value.t)
      (k : Value.t -> M.t)
      (output_inter : option (Value.t * State))
      (state_in : State) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ p, state_in ⏩ f args 🔽 output_inter }} ->
    match output_inter with
    | Some (value_inter, state_inter) =>
      {{ p, state_inter ⏩ k value_inter 🔽 output }}
    | None =>
      output = None
    end ->
    {{ p, state_in ⏩ M.CallClosure closure args k 🔽 output }} *)
  | LetSuccess
      (e : M.t)
      (k : Value.t -> M.t)
      (value_inter : Value.t)
      (state_inter : State)
      (state_in : State) :
    {{ p, state_in ⏩ e 🔽 Some (value_inter, state_inter) }} ->
    {{ p, state_inter ⏩ k value_inter 🔽 output }} ->
    {{ p, state_in ⏩ M.Let e k 🔽 output }}
  | LetPanic
      (e : M.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    output = None ->
    {{ p, state_in ⏩ e 🔽 None }} ->
    {{ p, state_in ⏩ M.Let e k 🔽 output }}
  | LetUnfold
      (e : M.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    {{ p, state_in ⏩ M.let_ e k 🔽 output }} ->
    {{ p, state_in ⏩ M.Let e k 🔽 output }}
  | LetUnUnfold
      (e : M.t)
      (k : Value.t -> M.t)
      (state_in : State) :
    {{ p, state_in ⏩ M.Let e k 🔽 output }} ->
    {{ p, state_in ⏩ M.let_ e k 🔽 output }}

  where "{{ p , state_in ⏩ e 🔽 output }}" :=
    (t p output state_in e).

  Lemma Let {State Address : Set} `{State.Trait State Address} {p : Z}
      (e : M.t)
      (k : Value.t -> M.t)
      (output_inter output : option (Value.t * State))
      (state_in : State) :
    {{ p, state_in ⏩ e 🔽 output_inter }} ->
    match output_inter with
    | Some (value_inter, state_inter) =>
      {{ p, state_inter ⏩ k value_inter 🔽 output }}
    | None =>
      output = None
    end ->
    {{ p, state_in ⏩ M.Let e k 🔽 output }}.
  Proof.
    intros H_e H_k.
    destruct output_inter as [ [] |].
    { eapply LetSuccess.
      { apply H_e. }
      { apply H_k. }
    }
    { now eapply LetPanic. }
  Qed.

  (* Lemma PureExact {State Address : Set} `{State.Trait State Address}
      (p : Z) (output : Result.t) (state : State) :
    {{ p, state ⏩ M.Pure output 🔽 output ⏩ fun state' => state' = state }}.
  Proof.
    now apply Pure.
  Qed. *)

  (* Lemma PureImplies {State Address : Set} `{State.Trait State Address}
      (p : Z) (output output' : Result.t) (P_state P_state' : State -> Prop) :
    output = output' ->
    (state = state') ->
    {{ p, state ⏩ LowM.Pure output 🔽 output' ⏩ state' }}.
  Proof.
    intros -> ->.
    apply Pure.
  Qed. *)

  (* Lemma For_aux {State Address : Set} `{State.Trait State Address}
      (p : Z) (state_in : State)
      (integer_kind : IntegerKind.t) (start : Z) (len : nat) (body : Value.t -> M.t)
      {Accumulator : Set}
      (inject : State -> Accumulator -> State)
      (accumulator_in : Accumulator)
      (body_expression : Z -> MS! Accumulator unit)
      (H_body : forall (accumulator_in : Accumulator) (i : Z),
        let output_accumulator_out := body_expression i accumulator_in in
        {{ p, inject state_in accumulator_in ⏩
          body (M.alloc (Value.Integer integer_kind i)) 🔽
          Panic.to_result_alloc (fst output_accumulator_out)
        ⏩ inject state_in (snd output_accumulator_out) }}
      ) :
    let output_accumulator_out :=
      foldS!
        tt
        (List.map (fun offset => start + Z.of_nat offset) (List.seq 0 len))
        (fun (_ : unit) => body_expression)
        accumulator_in in
    {{ p, inject state_in accumulator_in ⏩
      M.for_
        (Value.Integer integer_kind start)
        (Value.Integer integer_kind (start + Z.of_nat len))
        body 🔽
      Panic.to_result_alloc (fst output_accumulator_out)
    ⏩ inject state_in (snd output_accumulator_out) }}.
  Proof.
    revert start accumulator_in.
    induction len as [| len IHlen]; intros; unfold M.for_, M.for_Z in *; simpl in *.
    { replace (start + 0) with start by lia.
      replace (start - start) with 0 by lia.
      apply Pure.
    }
    { replace (Z.to_nat (start + _ - start)) with (S len) by lia.
      simpl.
      apply LetUnUnfold.
      eapply Let. {
        apply H_body.
      }
      replace (start + _ - _) with start by lia.
      unfold output_accumulator_out.
      replace (start + 0) with start by lia.
      unfold StatePanic.bind.
      destruct body_expression as [output accumulator_out]; simpl.
      destruct output as [ [] |]; simpl.
      { replace (start + Z.pos _) with (start + 1 + Z.of_nat len) by lia.
        pose proof (IHlen (start + 1) accumulator_out) as IHlen'.
        replace ((start + 1) + _ - (start + 1)) with (Z.of_nat len) in IHlen' by lia.
        replace (Z.to_nat (Z.of_nat len)) with len in IHlen' by lia.
        assert (H_map_seq_one :
          List.map (fun offset : nat => start + Z.of_nat offset) (List.seq 1 len) =
          List.map (fun offset : nat => start + 1 + Z.of_nat offset) (List.seq 0 len)
        ). {
          clear.
          generalize 0%nat as n.
          induction len; simpl; [reflexivity|]; intros.
          rewrite <- IHlen.
          f_equal.
          lia.
        }
        rewrite <- H_map_seq_one in IHlen'.
        apply IHlen'.
      }
      { apply Run.Pure. }
    }
  Qed.

  Lemma For {State Address : Set} `{State.Trait State Address}
    (p : Z) (state_in : State)
    (integer_kind : IntegerKind.t) (start_z : Z) (len : nat) (body : Value.t -> M.t)
    (start end_ : Value.t)
    {Accumulator : Set}
    (inject : State -> Accumulator -> State)
    (accumulator_in : Accumulator)
    (body_expression : Z -> MS! Accumulator unit)
    (H_body : forall (accumulator_in : Accumulator) (i : Z),
      let output_accumulator_out := body_expression i accumulator_in in
      {{ p, inject state_in accumulator_in ⏩
        body (M.alloc (Value.Integer integer_kind i)) 🔽
        Panic.to_result_alloc (fst output_accumulator_out)
      ⏩ inject state_in (snd output_accumulator_out) }}
    ) :
  let output_accumulator_out :=
    foldS!
      tt
      (List.map (fun offset => start_z + Z.of_nat offset) (List.seq 0 len))
      (fun (_ : unit) => body_expression)
      accumulator_in in
  state_in = inject state_in accumulator_in ->
  start = Value.Integer integer_kind start_z ->
  end_ = Value.Integer integer_kind (start_z + Z.of_nat len) ->
  {{ p, state_in ⏩
    M.for_ start end_ body 🔽
    Panic.to_result_alloc (fst output_accumulator_out)
  ⏩ inject state_in (snd output_accumulator_out) }}.
  Proof.
    hauto q: on use: For_aux.
  Qed. *)
End Run.
Export Run.

Module Singleton.
  Module State.
    Definition t : Set := option Value.t.
  End State.

  Module Address.
    Definition t : Set := unit.
  End Address.

  Global Instance IsState : State.Trait State.t Address.t := {
    read state _ := state;
    alloc_write state _ value := Some (Some value);
  }.

  Lemma IsStateValid : State.Valid.t IsState.
  Proof.
    sauto lq: on rew: off.
  Qed.
End Singleton.

Module Field.
  Module Valid.
    Definition t (p : Z) (x : Field.t) : Prop :=
      0 <= x.(Field.value) < p.
  End Valid.
End Field.

Module Integer.
  Module Valid.
    Definition t {A : Set} `{BinaryInteger.C A} (x : A) : Prop :=
      BinaryInteger.min (Self := A) <= BinaryInteger.to_Z x <= BinaryInteger.max (Self := A).
  End Valid.
End Integer.

Module Array.
  Module Valid.
    Record t {A : Set} {size : U32.t} (P_A : A -> Prop) (array : Array.t A size) : Prop := {
      length : List.length array.(Array.value) = Z.to_nat size.(Integer.value);
      elements : List.Forall P_A array.(Array.value);
    }.
  End Valid.

  Lemma listUpdate_error_map {A B : Set} (f : A -> B) (l : list A) (i : nat) (v : A) (v' : B) :
    v' = f v ->
    List.listUpdate_error (List.map f l) i v' =
    match List.listUpdate_error l i v with
    | Some l' => Some (List.map f l')
    | None => None
    end.
  Admitted.

  Lemma list_nth_error_listUpdate_error {A : Set} (l : list A) (i : nat) (v : A) :
    match List.nth_error l i, List.listUpdate_error l i v with
    | None, None | Some _, Some _ => True
    | _, _ => False
    end.
  Admitted.
End Array.

(** Some rewrites for the basic operations *)
Module Rewrites.
  (* Axiom rewrite_add_field : forall (kind : IntegerKind.t) (x y : Z),
    Binary.add (Value.Integer kind x) (Value.Integer kind y) =
    match kind with
    | IntegerKind.Field =>
      LowM.CallPrimitive Primitive.GetFieldPrime (fun p =>
        M.pure (Value.Integer IntegerKind.Field ((x + y) mod p))
      )
    | IntegerKind.U1 =>
      M.pure (
          Value.Integer kind (BinaryInteger.add (Self := Integer.t IntegerKind.U1)
          {| Integer.value := x |} {| Integer.value := y |}
        ).(Integer.value)
      )
    | _ => M.impossible "add: expected integer values"
    end.

  Axiom rewrite_subtract : forall (kind : IntegerKind.t) (x y : Z),
    Binary.subtract (Value.Integer kind x) (Value.Integer kind y) =
    Value.Integer kind (x - y).
    
    
      M.pure (Value.Integer kind (x + y))
    | _, _ => impossible "add: expected integer values"
    end. *)
End Rewrites.
