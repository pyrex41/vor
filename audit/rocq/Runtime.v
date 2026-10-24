From Coq Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

(* Parameterized by the frozen R03 step/outcome operations. This proves the
   finite path walk, not the correctness of the step dispatcher or host. *)
Section Runtime.
  Context {State Outcome : Type}.
  Variable state_eq : forall a b : State, {a=b}+{a<>b}.
  Variable outcome_eq : forall a b : Outcome, {a=b}+{a<>b}.
  Variable step : State -> State.
  Variable outcome : State -> option Outcome.

  Inductive path : State -> list State -> Outcome -> Prop :=
  | path_done : forall s o, outcome s = Some o -> path s [] o
  | path_next : forall s t rest o,
      outcome s = None -> t = step s -> path t rest o -> path s (t::rest) o.

  Fixpoint check_path fuel current rest expected {struct rest} : bool :=
    match outcome current with
    | Some actual => match rest with
                     | [] => if outcome_eq actual expected then true else false
                     | _ => false end
    | None => match rest, fuel with
              | next::tail, S n =>
                if state_eq next (step current)
                then check_path n next tail expected else false
              | _, _ => false end
    end.

  Theorem path_checker_sound : forall rest fuel current expected,
    check_path fuel current rest expected = true -> path current rest expected.
  Proof.
    induction rest as [|next rest IH]; intros fuel current expected H;
      simpl in H; destruct (outcome current) as [actual|] eqn:O.
    - destruct (outcome_eq actual expected); try discriminate. subst; constructor; auto.
    - destruct fuel; discriminate.
    - discriminate.
    - destruct fuel; try discriminate.
      destruct (state_eq next (step current)); try discriminate.
      econstructor; eauto.
  Qed.

  Theorem path_checker_complete : forall current rest expected,
    path current rest expected -> forall fuel,
    length rest <= fuel -> check_path fuel current rest expected = true.
  Proof.
    intros current rest expected H. induction H; intros fuel F; simpl.
    - rewrite H. destruct (outcome_eq o o); congruence.
    - rewrite H. destruct fuel; simpl in F; try lia.
      destruct (state_eq t (step s)); try congruence.
      apply IHpath; simpl in F; lia.
  Qed.

  Theorem path_outcome_unique : forall s xs ys a b,
    path s xs a -> path s ys b -> a = b.
  Proof.
    intros s xs ys a b H. revert ys b.
    induction H; intros ys b K; inversion K; subst; try congruence.
    eauto.
  Qed.

  Fixpoint run fuel s : option (Outcome * list State) :=
    match outcome s with
    | Some o => Some (o, [])
    | None => match fuel with
              | 0 => None
              | S n => match run n (step s) with
                       | Some (o, states) => Some (o, step s::states)
                       | None => None end
              end
    end.

  Theorem runner_sound : forall fuel s o states,
    run fuel s = Some (o,states) -> path s states o /\ length states <= fuel.
  Proof.
    induction fuel; intros s o states H; simpl in H;
      destruct (outcome s) as [actual|] eqn:O; try discriminate.
    - inversion H; subst. split; [constructor; auto | simpl; lia].
    - inversion H; subst. split; [constructor; auto | simpl; lia].
    - destruct (run fuel (step s)) as [[v xs]|] eqn:R; try discriminate.
      inversion H; subst. apply IHfuel in R as [HP HF].
      split; [econstructor; eauto | simpl; lia].
  Qed.

  Corollary runner_receipt_accepted : forall fuel s o states,
    run fuel s = Some (o,states) -> check_path fuel s states o = true.
  Proof.
    intros. apply runner_sound in H as [P F]. eapply path_checker_complete; eauto.
  Qed.
End Runtime.
