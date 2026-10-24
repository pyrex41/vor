From Coq Require Import List.
From VorAudit Require Import Compiler.
Import ListNotations.
Set Implicit Arguments.

(* R03 expression/argument/let control for the R05 fragment. A whole callee is
   summarized by the SAME fixed call oracle as the big-step and bytecode models.
   Ordered clause selection/guards are not hidden in this theorem. *)
Section CEK.
Variable call : nat -> list value -> option value.
Inductive destination := PrimitiveCons | User (name : nat).
Inductive frame := Bind (body : expr) (env : list value)
  | Argument (target : destination) (rest : exprs) (env done : list value).
Inductive control := Eval (e : expr) (env : list value)
  | Ret (v : value)
  | Args (target : destination) (rest : exprs) (env done : list value)
  | Dispatch (target : destination) (values : list value).
Definition state := (control * list frame)%type.
Definition step (s : state) : option state :=
  let '(c,k) := s in
  match c with
  | Eval (Literal v) env => Some (Ret v,k)
  | Eval (Local i) env => match nth_error env i with Some v => Some (Ret v,k) | None => None end
  | Eval (MakeCons a b) env => Some (Args PrimitiveCons (Arg a (Arg b NoArgs)) env [],k)
  | Eval (LetIn a b) env => Some (Eval a env,Bind b env::k)
  | Eval (Invoke f es) env => Some (Args (User f) es env [],k)
  | Ret v => match k with
      | [] => None
      | Bind b env::rest => Some (Eval b (v::env),rest)
      | Argument d es env done::rest => Some (Args d es env (done++[v]),rest)
      end
  | Args d NoArgs env done => Some (Dispatch d done,k)
  | Args d (Arg e es) env done => Some (Eval e env,Argument d es env done::k)
  | Dispatch PrimitiveCons [a;b] => Some (Ret (Cons a b),k)
  | Dispatch (User f) values => match call f values with Some v => Some (Ret v,k) | None => None end
  | _ => None
  end.
Inductive steps : state -> state -> Prop :=
| steps_refl : forall s, steps s s
| steps_next : forall s mid final, step s = Some mid -> steps mid final -> steps s final.
Lemma steps_trans : forall a b c, steps a b -> steps b c -> steps a c.
Proof. intros a b c E; induction E; intros F; eauto using steps. Qed.

Theorem evaluator_adequacy :
  (forall env e v, evaluates call env e v -> forall k,
    steps (Eval e env,k) (Ret v,k)) /\
  (forall env es vs, evaluates_args call env es vs -> forall d done k,
    steps (Args d es env done,k) (Dispatch d (done++vs),k)).
Proof.
  apply evaluation_induction; intros.
  - eapply steps_next; [reflexivity | constructor].
  - eapply steps_next; [simpl; rewrite e; reflexivity | constructor].
  - eapply steps_next; [reflexivity |].
    eapply steps_next; [reflexivity |].
    eapply steps_trans; [apply H |].
    eapply steps_next; [reflexivity |].
    eapply steps_next; [reflexivity |].
    eapply steps_trans; [apply H0 |].
    eapply steps_next; [reflexivity |].
    eapply steps_next; [reflexivity |].
    eapply steps_next; [reflexivity | constructor].
  - eapply steps_next; [reflexivity |].
    eapply steps_trans; [apply H |].
    eapply steps_next; [reflexivity | apply H0].
  - eapply steps_next; [reflexivity |].
    eapply steps_trans; [apply H |].
    simpl. eapply steps_next; [simpl; rewrite e0; reflexivity | constructor].
  - rewrite app_nil_r. eapply steps_next; [reflexivity | constructor].
  - eapply steps_next; [reflexivity |].
    eapply steps_trans; [apply H |].
    eapply steps_next; [reflexivity |].
    replace (done ++ v :: vs) with ((done ++ [v]) ++ vs) by (rewrite <- app_assoc; reflexivity).
    apply H0.
Qed.

Lemma terminal_no_step : forall v, step (Ret v,[]) = None.
Proof. reflexivity. Qed.

Theorem final_result_unique : forall s a b,
  steps s (Ret a,[]) -> steps s (Ret b,[]) -> a=b.
Proof.
  intros s a b E. remember (Ret a,[]) as final eqn:F.
  revert b a F. induction E; intros b a F Other; subst.
  - inversion Other; subst; try congruence; try solve [simpl in *; discriminate].
  - inversion Other; subst; try congruence; try solve [simpl in *; discriminate].
    assert (mid = mid0) by congruence. subst mid0. eapply IHE; eauto.
Qed.

Corollary adequacy_all_outcomes : forall env e a b,
  evaluates call env e a -> steps (Eval e env,[]) (Ret b,[]) -> a=b.
Proof.
  intros. eapply final_result_unique; [apply (proj1 evaluator_adequacy); eauto | eauto].
Qed.
End CEK.
