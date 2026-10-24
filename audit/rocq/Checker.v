From Coq Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

(* The threaded-node budget and ordered-premise control used by fol-derive/run.
   Rule semantics are an explicit parameter, not a fabricated soundness axiom. *)
Section Scheduler.
  Context {Goal : Type} (expand : Goal -> option (list Goal)).
  Fixpoint check (fuel : nat) (work : list Goal) : option nat :=
    match work with
    | [] => Some fuel
    | g :: rest =>
      match fuel with
      | 0 => None
      | S n => match expand g with
               | None => None
               | Some children => check n (children ++ rest)
               end
      end
    end.

  Inductive Derives : Goal -> Prop :=
  | derives_node : forall g ps,
      expand g = Some ps -> Forall Derives ps -> Derives g.

  Lemma check_remainder : forall fuel work rem,
    check fuel work = Some rem -> rem <= fuel.
  Proof.
    induction fuel; intros [|g gs] rem H; simpl in H;
      try discriminate; try (inversion H; lia).
    destruct (expand g) eqn:E; try discriminate.
    specialize (IHfuel _ _ H). lia.
  Qed.

  Theorem check_derivation : forall fuel work rem,
    check fuel work = Some rem -> Forall Derives work.
  Proof.
    induction fuel; intros [|g gs] rem H; simpl in H;
      try discriminate; try solve [constructor].
    destruct (expand g) as [ps|] eqn:E; try discriminate.
    specialize (IHfuel _ _ H).
    apply Forall_app in IHfuel as [HP HR].
    constructor; [econstructor; eauto | exact HR].
  Qed.

  Theorem check_sound (Valid : Goal -> Prop)
      (local_sound : forall g ps, expand g = Some ps ->
                       Forall Valid ps -> Valid g) :
    forall fuel work rem,
      check fuel work = Some rem -> Forall Valid work.
  Proof.
    induction fuel; intros [|g gs] rem H; simpl in H;
      try discriminate; try solve [constructor].
    destruct (expand g) as [ps|] eqn:E; try discriminate.
    specialize (IHfuel _ _ H).
    apply Forall_app in IHfuel as [HP HR].
    constructor; [eapply local_sound; eauto | exact HR].
  Qed.

  Lemma check_nil : forall fuel, check fuel [] = Some fuel.
  Proof. destruct fuel; reflexivity. Qed.

  Theorem check_budget_extension : forall fuel work rem extra,
    check fuel work = Some rem ->
    check (fuel + extra) work = Some (rem + extra).
  Proof.
    induction fuel; intros [|g gs] rem extra H; simpl in H.
    - inversion H; subst. rewrite check_nil. reflexivity.
    - discriminate.
    - inversion H; subst. rewrite check_nil. reflexivity.
    - simpl. destruct (expand g) eqn:E; try discriminate.
      eapply IHfuel; eauto.
  Qed.

  Theorem zero_budget_nonempty : forall g rest,
    check 0 (g :: rest) = None.
  Proof. reflexivity. Qed.
End Scheduler.
