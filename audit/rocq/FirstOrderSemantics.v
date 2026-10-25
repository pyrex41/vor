From Coq Require Import List Arith Lia Bool.
From VorAudit Require Import FirstOrderSyntax.
Import ListNotations.
Set Implicit Arguments.

Record signature := Sig {
  function_signature : nat -> option (list nat * nat);
  predicate_signature : nat -> option (list nat);
  declared_sort : nat -> bool
}.
Fixpoint term_sort (sig : signature) (vars : list nat) (t : term) : option nat :=
  match t with
  | Var n => nth_error vars n
  | App f ts => match function_signature sig f with
      | Some (ss,s) => if arguments_typed sig vars ts ss then Some s else None
      | None => None end
  end
with arguments_typed (sig : signature) (vars : list nat) (ts : terms) (ss : list nat) : bool :=
  match ts,ss with
  | TNil,[] => true
  | TCons t rest,s::ss => match term_sort sig vars t with
      | Some found => (found =? s) && arguments_typed sig vars rest ss
      | None => false end
  | _,_ => false end.
Definition has_type sig vars t sort :=
  match term_sort sig vars t with Some found => found =? sort | None => false end.
Fixpoint formula_typed sig vars p :=
  match p with
  | Top | Bottom => true
  | Pred f ts => match predicate_signature sig f with
      Some ss => arguments_typed sig vars ts ss | None => false end
  | Equal s a b => declared_sort sig s && has_type sig vars a s && has_type sig vars b s
  | And p q | Or p q | Imp p q => formula_typed sig vars p && formula_typed sig vars q
  | All s p | Ex s p => declared_sort sig s && formula_typed sig (s::vars) p
  end.
Definition sequent_typed sig vars gamma p :=
  forallb (declared_sort sig) vars && forallb (formula_typed sig vars) gamma && formula_typed sig vars p.

Section Semantics.
Context {D : Type}.
Variable fn : nat -> list D -> D.
Variable pred : nat -> list D -> Prop.
Variable belongs : nat -> D -> Prop.
Definition env := nat -> D.
Definition extend (v : D) (rho : env) n := match n with 0 => v | S k => rho k end.
Fixpoint interpret_term t (rho : env) :=
  match t with Var n => rho n | App f ts => fn f (interpret_terms ts rho) end
with interpret_terms ts (rho : env) :=
  match ts with TNil => [] | TCons t rest => interpret_term t rho :: interpret_terms rest rho end.
Fixpoint denote p (rho : env) : Prop :=
  match p with
  | Top => True | Bottom => False | Pred f ts => pred f (interpret_terms ts rho)
  | Equal _ a b => interpret_term a rho = interpret_term b rho
  | And p q => denote p rho /\ denote q rho
  | Or p q => denote p rho \/ denote q rho
  | Imp p q => denote p rho -> denote q rho
  | All s p => forall v, belongs s v -> denote p (extend v rho)
  | Ex s p => exists v, belongs s v /\ denote p (extend v rho)
  end.
Definition holds gamma rho := Forall (fun p => denote p rho) gamma.
Definition environment_typed vars rho := forall n s, nth_error vars n = Some s -> belongs s (rho n).

Lemma environment_extend : forall vars rho s v,
  environment_typed vars rho -> belongs s v -> environment_typed (s::vars) (extend v rho).
Proof. intros vars rho s v E V [|n] sort H; simpl in *; [inversion H; subst | eapply E]; eauto. Qed.
Lemma term_extensional :
  (forall t rho eta, (forall n, rho n=eta n) -> interpret_term t rho=interpret_term t eta) /\
  (forall ts rho eta, (forall n, rho n=eta n) -> interpret_terms ts rho=interpret_terms ts eta).
Proof. apply term_induction; intros; simpl; f_equal; eauto. Qed.
Lemma denote_extensional : forall p rho eta,
  (forall n, rho n=eta n) -> (denote p rho <-> denote p eta).
Proof.
  induction p; intros rho eta E; simpl;
    try (repeat rewrite (proj1 term_extensional _ rho eta E));
    try rewrite (proj2 term_extensional _ rho eta E);
    
    try (rewrite (IHp1 rho eta E), (IHp2 rho eta E); tauto);
    try tauto.
  all: assert (B: forall v, denote p (extend v rho) <-> denote p (extend v eta))
    by (intros; apply IHp; intros [|n]; simpl; auto).
  all: firstorder.
Qed.

Theorem term_renaming :
  (forall t r rho, interpret_term (rename_term r t) rho = interpret_term t (fun n => rho (r n))) /\
  (forall ts r rho, interpret_terms (rename_terms r ts) rho = interpret_terms ts (fun n => rho (r n))).
Proof. apply term_induction; intros; simpl; f_equal; auto. Qed.
Theorem formula_renaming : forall p r rho,
  denote (rename r p) rho <-> denote p (fun n => rho (r n)).
Proof.
  induction p; intros r rho; simpl;
    try (repeat rewrite (proj1 term_renaming)); try rewrite (proj2 term_renaming);
    
    try (rewrite IHp1, IHp2; tauto); try tauto.
  all: assert (B: forall v,
    denote (rename (up r) p) (extend v rho) <->
    denote p (extend v (fun n => rho (r n)))).
  all: try (intro v; rewrite IHp; apply denote_extensional; intros [|n]; reflexivity).
  all: firstorder.
Qed.

Theorem term_substitution :
  (forall t s rho, interpret_term (subst_term s t) rho =
    interpret_term t (fun n => interpret_term (s n) rho)) /\
  (forall ts s rho, interpret_terms (subst_terms s ts) rho =
    interpret_terms ts (fun n => interpret_term (s n) rho)).
Proof. apply term_induction; intros; simpl; f_equal; auto. Qed.
Lemma lift_substitution_environment : forall s rho v n,
  interpret_term (up_sub s n) (extend v rho) = extend (interpret_term (Var 0) (extend v rho))
    (fun k => interpret_term (s k) rho) n.
Proof.
  intros s rho v [|n]; simpl; auto. unfold up_sub; simpl.
  rewrite (proj1 term_renaming). reflexivity.
Qed.
Theorem formula_substitution : forall p s rho,
  denote (subst s p) rho <-> denote p (fun n => interpret_term (s n) rho).
Proof.
  induction p; intros s rho; simpl;
    try (repeat rewrite (proj1 term_substitution)); try rewrite (proj2 term_substitution);
    
    try (rewrite IHp1, IHp2; tauto); try tauto.
  all: assert (B: forall v, denote (subst (up_sub s) p) (extend v rho) <->
    denote p (extend v (fun n => interpret_term (s n) rho))).
  all: try (intro v; rewrite IHp; apply denote_extensional; apply lift_substitution_environment).
  all: firstorder.
Qed.

Theorem weakening : forall p rho v,
  denote (shift p 1 0) (extend v rho) <-> denote p rho.
Proof.
  intros. unfold shift. rewrite formula_renaming. apply denote_extensional.
  intro n. unfold shift_index. simpl. replace (n+1) with (S n) by lia. reflexivity.
Qed.
Theorem binder_substitution : forall p t rho,
  denote (remove p t 0) rho <-> denote p (extend (interpret_term t rho) rho).
Proof.
  intros. unfold remove. rewrite formula_substitution. apply denote_extensional.
  intros [|n]; simpl; unfold remove_index; simpl; auto.
  unfold shift_term. rewrite (proj1 term_renaming). apply (proj1 term_extensional).
  intro k. unfold shift_index; simpl. rewrite Nat.add_0_r. reflexivity.
Qed.
Theorem context_weakening : forall gamma rho v,
  holds (map (fun p => shift p 1 0) gamma) (extend v rho) <-> holds gamma rho.
Proof.
  induction gamma; intros; unfold holds in *; simpl.
  - split; constructor.
  - rewrite !Forall_cons_iff, IHgamma, weakening. tauto.
Qed.

Variable sig : signature.
Hypothesis functions_typed : forall f ss s values,
  function_signature sig f = Some (ss,s) ->
  Forall2 belongs ss values -> belongs s (fn f values).
Theorem term_typing_sound :
  (forall t vars s, term_sort sig vars t = Some s -> forall rho,
    environment_typed vars rho -> belongs s (interpret_term t rho)) /\
  (forall ts vars ss, arguments_typed sig vars ts ss = true -> forall rho,
    environment_typed vars rho -> Forall2 belongs ss (interpret_terms ts rho)).
Proof.
  apply term_induction.
  - intros n vars s H rho E. eapply E; eauto.
  - intros f ts IH vars s H rho E. simpl in H.
    destruct (function_signature sig f) as [[ss result]|] eqn:F; try discriminate.
    destruct (arguments_typed sig vars ts ss) eqn:A; try discriminate.
    inversion H; subst. eapply functions_typed; eauto.
  - intros vars [|s ss] H rho E; simpl in H; try discriminate. constructor.
  - intros t IHt ts IHts vars [|s ss] H rho E; simpl in H; try discriminate.
    destruct (term_sort sig vars t) as [found|] eqn:T; try discriminate.
    apply andb_true_iff in H as [EQ A]. apply Nat.eqb_eq in EQ; subst found.
    constructor; eauto.
Qed.
Lemma has_type_sound : forall vars t s rho,
  has_type sig vars t s = true -> environment_typed vars rho -> belongs s (interpret_term t rho).
Proof.
  intros. unfold has_type in H. destruct (term_sort sig vars t) eqn:T; try discriminate.
  apply Nat.eqb_eq in H; subst. eapply (proj1 term_typing_sound); eauto.
Qed.
End Semantics.
