From Coq Require Import List Arith Lia Wf_nat Wellfounded.Inverse_Image.
Import ListNotations.
Set Implicit Arguments.

(* Earlier definition rank dominates arbitrary argument sizes; within the same
   definition the structural measure must strictly decrease. *)
Definition call_state := (nat * nat)%type.
Definition earlier (a b : call_state) : Prop :=
  fst a < fst b \/ (fst a = fst b /\ snd a < snd b).
Theorem earlier_well_founded : well_founded earlier.
Proof.
  intros [rank size]. revert size.
  induction rank as [rank IHrank] using lt_wf_ind. intros size.
  induction size as [size IHsize] using lt_wf_ind.
  constructor. intros [r m] L. unfold earlier in L; simpl in L.
  destruct L as [LR | [EQ LM]].
  - apply IHrank; exact LR.
  - subst r. apply IHsize; exact LM.
Qed.

Section Construction.
  Context {State Value : Type}.
  Variable rank measure : State -> nat.
  Definition precedes (a b : State) := earlier (rank a, measure a) (rank b, measure b).
  Lemma precedes_well_founded : well_founded precedes.
  Proof.
    exact (wf_inverse_image State call_state earlier (fun s => (rank s, measure s)) earlier_well_founded).
  Qed.
  Inductive body : Type :=
  | Return (v : Value)
  | Call (callee : State) (continue : Value -> body).
  Variable program : State -> body.
  Variable Post : State -> Value -> Prop.

  (* A genuinely finite derivation. Contracts justify a continuation only for
     results satisfying the *same callee's* contract, with exact value binding. *)
  Inductive constructs (current : State) : body -> Prop :=
  | construct_return : forall v, Post current v -> constructs current (Return v)
  | construct_call : forall callee k,
      precedes callee current ->
      (forall v, Post callee v -> constructs current (k v)) ->
      constructs current (Call callee k).

  Inductive eval_state : State -> Value -> Prop :=
  | eval_definition : forall s v, eval_body (program s) v -> eval_state s v
  with eval_body : body -> Value -> Prop :=
  | eval_return : forall v, eval_body (Return v) v
  | eval_call : forall callee k v result,
      eval_state callee v -> eval_body (k v) result -> eval_body (Call callee k) result.

  Lemma body_total : forall current,
    (forall callee, precedes callee current ->
      exists v, eval_state callee v /\ Post callee v) ->
    forall b, constructs current b -> exists v, eval_body b v /\ Post current v.
  Proof.
    intros current IH b C. induction C as [v P | callee k LT C IHC].
    - exists v. split; [constructor | exact P].
    - destruct (IH callee LT) as [v [EV PV]].
      destruct (IHC v PV) as [result [ER PR]].
      exists result. split; [econstructor; eauto | exact PR].
  Qed.

  Theorem admission_totality
    (constructed : forall s, constructs s (program s)) :
    forall s, exists v, eval_state s v /\ Post s v.
  Proof.
    apply (well_founded_induction precedes_well_founded
      (fun s => exists v, eval_state s v /\ Post s v)).
    intros s IH. destruct (body_total IH (constructed s)) as [v [EV PV]].
    exists v. split; [constructor; exact EV | exact PV].
  Qed.

  Lemma body_preservation : forall current,
    (forall callee, precedes callee current -> forall v,
      eval_state callee v -> Post callee v) ->
    forall b v, eval_body b v -> constructs current b -> Post current v.
  Proof.
    intros current IH b v E. induction E; intros C; inversion C; subst.
    - assumption.
    - apply IHE. apply H3. eapply IH; eauto.
  Qed.

  Theorem admission_all_outcomes
    (constructed : forall s, constructs s (program s)) :
    forall s v, eval_state s v -> Post s v.
  Proof.
    apply (well_founded_induction precedes_well_founded
      (fun s => forall v, eval_state s v -> Post s v)).
    intros s IH v E. inversion E; subst.
    eapply body_preservation; [exact IH | eassumption | apply constructed].
  Qed.

  Theorem admission_total_correct
    (constructed : forall s, constructs s (program s)) :
    (forall s, exists v, eval_state s v /\ Post s v) /\
    (forall s v, eval_state s v -> Post s v).
  Proof. split; [apply admission_totality | apply admission_all_outcomes]; assumption. Qed.
End Construction.
