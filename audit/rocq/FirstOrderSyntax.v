From Coq Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

(* Unambiguous raw sorted syntax. Lists are a separate strictly positive type
   to expose a complete mutual structural induction principle. *)
Inductive term := Var (n : nat) | App (name : nat) (args : terms)
with terms := TNil | TCons (head : term) (tail : terms).
Scheme term_ind_all := Induction for term Sort Prop
with terms_ind_all := Induction for terms Sort Prop.
Combined Scheme term_induction from term_ind_all, terms_ind_all.
Inductive formula :=
| Top | Bottom | Pred (name : nat) (args : terms)
| Equal (sort : nat) (left right : term)
| And (p q : formula) | Or (p q : formula) | Imp (p q : formula)
| All (sort : nat) (body : formula) | Ex (sort : nat) (body : formula).
Fixpoint term_eq_dec (x y : term) : {x=y}+{x<>y}
with terms_eq_dec (x y : terms) : {x=y}+{x<>y}.
Proof. all: decide equality; try apply Nat.eq_dec; auto. Defined.
Definition formula_eq_dec : forall x y : formula, {x=y}+{x<>y}.
Proof. decide equality; auto using Nat.eq_dec, term_eq_dec, terms_eq_dec. Defined.

Fixpoint rename_term (r : nat -> nat) (t : term) : term :=
  match t with Var n => Var (r n) | App f ts => App f (rename_terms r ts) end
with rename_terms (r : nat -> nat) (ts : terms) : terms :=
  match ts with TNil => TNil | TCons t rest => TCons (rename_term r t) (rename_terms r rest) end.
Definition up (r : nat -> nat) n := match n with 0 => 0 | S k => S (r k) end.
Fixpoint rename (r : nat -> nat) p :=
  match p with
  | Top => Top | Bottom => Bottom | Pred f ts => Pred f (rename_terms r ts)
  | Equal s a b => Equal s (rename_term r a) (rename_term r b)
  | And p q => And (rename r p) (rename r q)
  | Or p q => Or (rename r p) (rename r q)
  | Imp p q => Imp (rename r p) (rename r q)
  | All s p => All s (rename (up r) p)
  | Ex s p => Ex s (rename (up r) p)
  end.
Fixpoint subst_term (s : nat -> term) t :=
  match t with Var n => s n | App f ts => App f (subst_terms s ts) end
with subst_terms (s : nat -> term) ts :=
  match ts with TNil => TNil | TCons t rest => TCons (subst_term s t) (subst_terms s rest) end.
Definition up_sub (s : nat -> term) n :=
  match n with 0 => Var 0 | S k => rename_term S (s k) end.
Fixpoint subst (s : nat -> term) p :=
  match p with
  | Top => Top | Bottom => Bottom | Pred f ts => Pred f (subst_terms s ts)
  | Equal sort a b => Equal sort (subst_term s a) (subst_term s b)
  | And p q => And (subst s p) (subst s q)
  | Or p q => Or (subst s p) (subst s q)
  | Imp p q => Imp (subst s p) (subst s q)
  | All sort p => All sort (subst (up_sub s) p)
  | Ex sort p => Ex sort (subst (up_sub s) p)
  end.
Definition shift_index amount cut n := if cut <=? n then n + amount else n.
Definition shift_term t amount cut := rename_term (shift_index amount cut) t.
Definition shift p amount cut := rename (shift_index amount cut) p.
Definition remove_index t depth n :=
  if n =? depth then shift_term t depth 0 else Var (if depth <? n then pred n else n).
Definition remove_term p t depth := subst_term (remove_index t depth) p.
Definition remove p t depth := subst (remove_index t depth) p.

Lemma rename_terms_ext :
  (forall t r s, (forall n, r n = s n) -> rename_term r t = rename_term s t) /\
  (forall ts r s, (forall n, r n = s n) -> rename_terms r ts = rename_terms s ts).
Proof. apply term_induction; intros; simpl; f_equal; eauto. Qed.
Lemma rename_ext : forall p r s,
  (forall n, r n = s n) -> rename r p = rename s p.
Proof.
  induction p; intros r s E; simpl; f_equal; eauto using (proj1 rename_terms_ext), (proj2 rename_terms_ext).
  all: apply IHp; intros [|n]; simpl; auto.
Qed.
Lemma up_shift : forall a c n, up (shift_index a c) n = shift_index a (S c) n.
Proof. intros a c [|n]; unfold up, shift_index; simpl; auto. destruct (c <=? n); reflexivity. Qed.
Lemma shift_binder : forall s p a c,
  shift (All s p) a c = All s (shift p a (S c)).
Proof. intros; simpl; unfold shift; simpl; f_equal; apply rename_ext; apply up_shift. Qed.
Lemma shift_exists_binder : forall s p a c,
  shift (Ex s p) a c = Ex s (shift p a (S c)).
Proof. intros; unfold shift; simpl; f_equal; apply rename_ext; apply up_shift. Qed.

Lemma rename_comp :
  (forall t a b, rename_term a (rename_term b t) = rename_term (fun n => a (b n)) t) /\
  (forall ts a b, rename_terms a (rename_terms b ts) = rename_terms (fun n => a (b n)) ts).
Proof. apply term_induction; intros; simpl; f_equal; auto. Qed.
Lemma subst_ext : forall p a b,
  (forall n, a n = b n) -> subst a p = subst b p.
Proof.
  assert (T:
    (forall t a b, (forall n, a n=b n) -> subst_term a t=subst_term b t) /\
    (forall ts a b, (forall n, a n=b n) -> subst_terms a ts=subst_terms b ts)).
  { apply term_induction; intros; simpl; f_equal; eauto. }
  induction p; intros a b E; simpl; f_equal; eauto using (proj1 T), (proj2 T).
  all: apply IHp; intros [|n]; simpl; auto; unfold up_sub; simpl; rewrite E; reflexivity.
Qed.
Lemma up_remove : forall t d n,
  up_sub (remove_index t d) n = remove_index t (S d) n.
Proof.
  intros t d [|n]; unfold up_sub, remove_index; simpl; auto.
  destruct (n =? d) eqn:E.
  - unfold shift_term. rewrite (proj1 rename_comp).
    apply (proj1 rename_terms_ext). intros k. unfold shift_index; simpl; lia.
  - destruct (d <? n) eqn:L; simpl; f_equal.
    + apply Nat.ltb_lt in L. destruct (S d <? S n) eqn:M;
        [apply Nat.ltb_lt in M | apply Nat.ltb_ge in M]; lia.
    + apply Nat.ltb_ge in L. destruct (S d <? S n) eqn:M;
        [apply Nat.ltb_lt in M | apply Nat.ltb_ge in M]; lia.
Qed.
Lemma remove_binder : forall sort p t d,
  remove (All sort p) t d = All sort (remove p t (S d)).
Proof. intros; unfold remove; simpl; f_equal; apply subst_ext; apply up_remove. Qed.
Lemma remove_exists_binder : forall sort p t d,
  remove (Ex sort p) t d = Ex sort (remove p t (S d)).
Proof. intros; unfold remove; simpl; f_equal; apply subst_ext; apply up_remove. Qed.

Lemma substitution_of_variables :
  (forall t s r, (forall n,s n=Var(r n)) -> subst_term s t=rename_term r t) /\
  (forall ts s r, (forall n,s n=Var(r n)) -> subst_terms s ts=rename_terms r ts).
Proof.
  apply term_induction; intros; simpl; [apply H | f_equal; eauto | reflexivity | f_equal; eauto].
Qed.
Lemma formula_substitution_of_variables : forall p s r,
  (forall n,s n=Var(r n)) -> subst s p=rename r p.
Proof.
  induction p; intros s r E; simpl; f_equal;
    eauto using (proj1 substitution_of_variables), (proj2 substitution_of_variables).
  all: apply IHp; intros [|n]; unfold up_sub,up; simpl; auto; rewrite E; reflexivity.
Qed.
