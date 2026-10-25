From Coq Require Import List Arith Bool Lia.
From VorAudit Require Import Checker FirstOrderSyntax FirstOrderSemantics.
Import ListNotations.
Set Implicit Arguments.

Inductive proof :=
| Hyp (n:nat) | Unit | Pair (a b:proof)
| Fst (q:formula) (e:proof) | Snd (p:formula) (e:proof)
| Intro (e:proof) | Apply (p:formula) (a b:proof)
| Inl (e:proof) | Inr (e:proof)
| Cases (p q:formula) (e a b:proof) | Exfalso (e:proof)
| Gen (e:proof) | Inst (s:nat) (body:formula) (t:term) (e:proof)
| Witness (t:term) (e:proof) | Unpack (s:nat) (body:formula) (e branch:proof)
| Refl | Sym (e:proof) | Trans (mid:term) (a b:proof)
| Subst (s:nat) (motive:formula) (left right:term) (eq body:proof)
| TreeInduct (base step:proof) | Unsupported.
Record goal := G { vars:list nat; gamma:list formula; target:formula; evidence:proof }.
Definition raised gamma n := map (fun p => shift p n 0) gamma.
Definition instance sig v sort body t p :=
  declared_sort sig sort && formula_typed sig (sort::v) body && has_type sig v t sort &&
    if formula_eq_dec p (remove body t 0) then true else false.
Definition raw_expand sig g : option (list goal) :=
  let '(G v gamma p e) := g in
  match e with
  | Hyp n => match nth_error gamma n with Some q => if formula_eq_dec p q then Some [] else None | None => None end
  | Unit => match p with Top => Some [] | _ => None end
  | Pair a b => match p with And l r => Some [G v gamma l a; G v gamma r b] | _ => None end
  | Fst q e => if formula_typed sig v q then Some [G v gamma (And p q) e] else None
  | Snd q e => if formula_typed sig v q then Some [G v gamma (And q p) e] else None
  | Intro e => match p with Imp l r => Some [G v (l::gamma) r e] | _ => None end
  | Apply q a b => if formula_typed sig v q then Some [G v gamma (Imp q p) a; G v gamma q b] else None
  | Inl e => match p with Or l r => Some [G v gamma l e] | _ => None end
  | Inr e => match p with Or l r => Some [G v gamma r e] | _ => None end
  | Cases l r e a b => if formula_typed sig v l && formula_typed sig v r
      then Some [G v gamma (Or l r) e; G v (l::gamma) p a; G v (r::gamma) p b] else None
  | Exfalso e => Some [G v gamma Bottom e]
  | Gen e => match p with All s body => Some [G (s::v) (raised gamma 1) body e] | _ => None end
  | Inst s body t e => if instance sig v s body t p then Some [G v gamma (All s body) e] else None
  | Witness t e => match p with Ex s body => if has_type sig v t s then Some [G v gamma (remove body t 0) e] else None | _ => None end
  | Unpack s body e branch => if declared_sort sig s && formula_typed sig (s::v) body
      then Some [G v gamma (Ex s body) e; G (s::v) (body::raised gamma 1) (shift p 1 0) branch] else None
  | Refl => match p with Equal s a b => if term_eq_dec a b then Some [] else None | _ => None end
  | Sym e => match p with Equal s a b => Some [G v gamma (Equal s b a) e] | _ => None end
  | Trans mid a b => match p with Equal s l r => if has_type sig v mid s
      then Some [G v gamma (Equal s l mid) a; G v gamma (Equal s mid r) b] else None | _ => None end
  | Subst s motive l r eq body => if instance sig v s motive r p && has_type sig v l s
      then Some [G v gamma (Equal s l r) eq; G v gamma (remove motive l 0) body] else None
  | TreeInduct base step => match p with All 0 body =>
      let lifted := shift body 2 1 in
      Some [G v gamma (remove body (App 1 TNil) 0) base;
        G (0::0::v) (remove lifted (Var 1) 0 :: remove lifted (Var 0) 0 :: raised gamma 2)
          (remove lifted (App 2 (TCons (Var 1) (TCons (Var 0) TNil))) 0) step]
      | _ => None end
  | Unsupported => None
  end.
Definition expand sig g :=
  if sequent_typed sig (vars g) (gamma g) (target g) then raw_expand sig g else None.

Inductive tree := Leaf | Node (left right:tree).
Section Soundness.
Context {D:Type}.
Variable fn : nat -> list D -> D.
Variable pred : nat -> list D -> Prop.
Variable belongs : nat -> D -> Prop.
Variable sig : signature.
Hypothesis functions_typed : forall f ss s values,
  function_signature sig f = Some (ss,s) -> Forall2 belongs ss values -> belongs s (fn f values).
Variable encode_tree : tree -> D.
Hypothesis tree_values : forall v, belongs 0 v <-> exists t, encode_tree t = v.
Hypothesis tree_leaf : fn 1 [] = encode_tree Leaf.
Hypothesis tree_node : forall l r, fn 2 [encode_tree l; encode_tree r] = encode_tree (Node l r).
Definition valid g := forall rho,
  environment_typed belongs (vars g) rho -> holds fn pred belongs (gamma g) rho -> denote fn pred belongs (target g) rho.
Lemma instance_semantics : forall v s body t p,
  instance sig v s body t p = true -> forall rho,
  (denote fn pred belongs p rho <-> denote fn pred belongs body (extend (interpret_term fn t rho) rho)).
Proof.
  intros v s body t p H rho. unfold instance in H.
  repeat apply andb_true_iff in H as [H ?].
  destruct (formula_eq_dec p (remove body t 0)); try discriminate. subst.
  apply binder_substitution.
Qed.
Lemma instance_sorted : forall v s body t p,
  instance sig v s body t p = true -> has_type sig v t s = true.
Proof. intros. unfold instance in H. repeat rewrite andb_true_iff in H. tauto. Qed.
Lemma hypotheses_cons : forall p gamma rho,
  holds fn pred belongs (p::gamma) rho <-> denote fn pred belongs p rho /\ holds fn pred belongs gamma rho.
Proof. intros; apply Forall_cons_iff. Qed.
Lemma raised_two : forall gamma rho a b,
  holds fn pred belongs (raised gamma 2) (extend b (extend a rho)) <-> holds fn pred belongs gamma rho.
Proof.
  intros gs. induction gs as [|p gs IH]; intros rho a b; unfold raised, holds in *; simpl.
  - split; constructor.
  - rewrite !Forall_cons_iff.
    assert (P:denote fn pred belongs (shift p 2 0) (extend b (extend a rho)) <-> denote fn pred belongs p rho).
    { unfold shift. rewrite formula_renaming. apply denote_extensional.
      intro n. unfold shift_index; simpl. replace (n+2) with (S (S n)) by lia. reflexivity. }
    rewrite P, IH. tauto.
Qed.
Lemma lifted_motive : forall p rho x a b,
  denote fn pred belongs (shift p 2 1) (extend x (extend b (extend a rho))) <->
  denote fn pred belongs p (extend x rho).
Proof.
  intros. unfold shift. rewrite formula_renaming. apply denote_extensional.
  intros [|n]; unfold shift_index; simpl; auto.
  replace (n+2) with (S (S n)) by lia. reflexivity.
Qed.

Ltac premises := repeat match goal with
  | H:Forall _ (_::_) |- _ => inversion H; subst; clear H
  | H:Forall _ [] |- _ => clear H
  end.
Ltac boolean_guards := repeat match goal with
  | H: (if ?b then _ else _) = Some _ |- _ => destruct b eqn:?; try discriminate
  end.

Theorem expand_sound : forall g ps,
  expand sig g = Some ps -> Forall valid ps -> valid g.
Proof.
  intros [v gamma p e] ps E H.
  unfold expand in E; simpl in E.
  destruct (sequent_typed sig v gamma p) eqn:WF; try discriminate.
  unfold raw_expand in E; simpl in E. destruct e; simpl in E.
  - destruct (nth_error gamma n) as [q|] eqn:N; try discriminate.
    destruct (formula_eq_dec p q); try discriminate. subst q.
    unfold valid; simpl. intros rho ENV HG. unfold holds in HG. rewrite Forall_forall in HG. apply HG. eapply nth_error_In; eauto.
  - destruct p; try discriminate. unfold valid; simpl; auto.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. firstorder.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. intros rho ENV HG HP.
    apply H2 with (rho:=rho); auto. apply Forall_cons; assumption.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG. destruct (H2 rho ENV HG) as [L|R].
    + apply H1 with (rho:=rho); auto. constructor; auto.
    + apply H3 with (rho:=rho); auto. constructor; auto.
  - inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG x SX. apply H2 with (rho:=extend x rho).
    + eapply environment_extend; eauto.
    + apply context_weakening; exact HG.
  - destruct (instance sig v s body t p) eqn:I; try discriminate.
    inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG. apply (proj2 (instance_semantics v s body t p I rho)).
    apply H2; auto. eapply has_type_sound; eauto using instance_sorted.
  - destruct p; try discriminate. boolean_guards. inversion E; subst. premises.
    unfold valid in *; simpl in *. intros rho ENV HG.
    exists (interpret_term fn t rho). split.
    + eapply has_type_sound; eauto.
    + apply binder_substitution. eapply H2; eauto.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG. destruct (H2 rho ENV HG) as [x [SX PX]].
    apply (proj1 (weakening fn pred belongs p rho x)). apply H1.
    + eapply environment_extend; eauto.
    + constructor; auto. apply context_weakening; exact HG.
  - destruct p; try discriminate. destruct (term_eq_dec left right); try discriminate.
    subst right. unfold valid; simpl; auto.
  - destruct p; try discriminate. inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG. specialize (H2 rho ENV HG). specialize (H1 rho ENV HG). congruence.
  - boolean_guards. inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG. apply andb_true_iff in Heqb as [I L].
    apply (proj2 (instance_semantics v s motive right p I rho)). specialize (H2 rho ENV HG).
    rewrite <- H2. apply binder_substitution. apply H1; auto.
  - destruct p; try discriminate. destruct sort; try discriminate.
    inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho ENV HG x SX. apply tree_values in SX as [tr <-].
    induction tr as [|l IHl r IHr].
    + rewrite <- tree_leaf. apply (proj1 (binder_substitution fn pred belongs p (App 1 TNil) rho)). apply H2; auto.
    + rewrite <- tree_node.
      apply (proj1 (lifted_motive p rho (fn 2 [encode_tree l;encode_tree r]) (encode_tree l) (encode_tree r))).
      apply (proj1 (binder_substitution fn pred belongs (shift p 2 1)
        (App 2 (TCons (Var 1) (TCons (Var 0) TNil))) (extend (encode_tree r) (extend (encode_tree l) rho)))). apply H1.
      * repeat apply environment_extend; auto; apply tree_values; eauto.
      * repeat constructor.
        -- apply binder_substitution. apply (proj2 (lifted_motive p rho (encode_tree l) (encode_tree l) (encode_tree r))); exact IHl.
        -- apply binder_substitution. apply (proj2 (lifted_motive p rho (encode_tree r) (encode_tree l) (encode_tree r))); exact IHr.
        -- apply raised_two; exact HG.
  - discriminate.
Qed.

Theorem checker_sound : forall fuel g rem,
  check (expand sig) fuel [g] = Some rem -> valid g.
Proof.
  intros. pose proof (@check_sound goal (expand sig) valid expand_sound _ _ _ H) as V.
  inversion V; auto.
Qed.
End Soundness.
