From Coq Require Import List Arith Bool.
From VorAudit Require Import NativeLookup FirstOrderSyntax FirstOrderEncoding.
Import ListNotations.
Set Implicit Arguments.
Module FS := FirstOrderSyntax.
Module FE := FirstOrderEncoding.
Module NV := NativeLookup.

(* Same raw constructor/cell traversal as spec/logic.shen, with explicit failure
   for unsupported raw shapes. Binder depth changes only under forall/exists. *)
Fixpoint walk_term (action:nat->nat->option NV.datum) depth raw : option NV.datum := match raw with
  | NV.Cell (NV.Sym 4) (NV.Cell (NV.Num n) NV.Nil)=>action depth n
  | NV.Cell (NV.Sym 5) (NV.Cell (NV.Sym f) (NV.Cell ts NV.Nil))=>
      option_map (fun ts=>FE.tagged 5 [NV.Sym f;ts]) (walk_terms action depth ts)
  |_=>None end
with walk_terms (action:nat->nat->option NV.datum) depth raw : option NV.datum := match raw with
  | NV.Nil=>Some NV.Nil
  | NV.Cell t ts=>FE.combine2 NV.Cell (walk_term action depth t) (walk_terms action depth ts)
  |_=>None end.
Fixpoint walk_formula (action:nat->nat->option NV.datum) depth raw : option NV.datum := match raw with
  | NV.Cell (NV.Sym 6) NV.Nil=>Some (FE.tagged 6 [])
  | NV.Cell (NV.Sym 7) NV.Nil=>Some (FE.tagged 7 [])
  | NV.Cell (NV.Sym 8) (NV.Cell (NV.Sym f) (NV.Cell ts NV.Nil))=>
      option_map (fun ts=>FE.tagged 8 [NV.Sym f;ts]) (walk_terms action depth ts)
  | NV.Cell (NV.Sym 9) (NV.Cell (NV.Sym s) (NV.Cell a (NV.Cell b NV.Nil)))=>
      FE.combine2 (fun a b=>FE.tagged 9 [NV.Sym s;a;b]) (walk_term action depth a) (walk_term action depth b)
  | NV.Cell (NV.Sym op) (NV.Cell a (NV.Cell b NV.Nil))=>match op with
      10|11|12=>FE.combine2 (fun a b=>FE.tagged op [a;b]) (walk_formula action depth a) (walk_formula action depth b)
      |13|14=>match a with NV.Sym s=>option_map (fun p=>FE.tagged op [NV.Sym s;p]) (walk_formula action (S depth) b) | _=>None end
      |_=>None end
  |_=>None end.

Lemma walk_term_refines : forall action sub,
  (forall d n, action d n=Some (FE.encode_term (sub d n))) ->
  (forall t d, walk_term action d (FE.encode_term t)=Some (FE.encode_term (FS.subst_term (sub d) t))) /\
  (forall ts d, walk_terms action d (FE.encode_terms ts)=Some (FE.encode_terms (FS.subst_terms (sub d) ts))).
Proof.
  intros action sub LAW. apply FS.term_induction; intros; simpl; unfold FE.tagged in *; simpl;
    rewrite ?H,?H0; try reflexivity. apply LAW.
Qed.
Lemma walk_formula_refines : forall action sub,
  (forall d n, action d n=Some (FE.encode_term (sub d n))) ->
  (forall d n, FS.up_sub (sub d) n=sub (S d) n) ->
  forall p d, walk_formula action d (FE.encode_formula p)=Some (FE.encode_formula (FS.subst (sub d) p)).
Proof.
  intros action sub LAW UP. induction p; intros d; simpl; unfold FE.tagged in *; simpl;
    rewrite ?(proj1 (walk_term_refines action sub LAW)), ?(proj2 (walk_term_refines action sub LAW)), ?IHp, ?IHp1, ?IHp2; try reflexivity.
  all: replace (FS.subst (FS.up_sub (sub d)) p) with (FS.subst (sub (S d)) p)
    by (apply FS.subst_ext; intro n; symmetry; apply UP).
  all: reflexivity.
Qed.
Definition shift_action amount depth n := Some (FE.encode_term (FS.Var (FS.shift_index amount depth n))).
Definition raw_shift_term raw amount depth := walk_term (shift_action amount) depth raw.
Definition raw_shift raw amount depth := walk_formula (shift_action amount) depth raw.
Theorem shift_term_refinement : forall t amount depth,
  raw_shift_term (FE.encode_term t) amount depth=Some (FE.encode_term (FS.shift_term t amount depth)).
Proof.
  intros. unfold raw_shift_term, FS.shift_term.
  rewrite (proj1 (walk_term_refines (shift_action amount) (fun d n=>FS.Var (FS.shift_index amount d n)) (fun d n=>eq_refl _))) .
  rewrite (proj1 FS.substitution_of_variables t (fun n=>FS.Var (FS.shift_index amount depth n))
    (FS.shift_index amount depth) (fun n=>eq_refl _)). reflexivity.
Qed.
Theorem shift_formula_refinement : forall p amount depth,
  raw_shift (FE.encode_formula p) amount depth=Some (FE.encode_formula (FS.shift p amount depth)).
Proof.
  intros. unfold raw_shift,FS.shift.
  erewrite walk_formula_refines with (sub:=fun d n=>FS.Var (FS.shift_index amount d n)).
  - rewrite (FS.formula_substitution_of_variables p (fun n=>FS.Var (FS.shift_index amount depth n))
      (FS.shift_index amount depth) (fun n=>eq_refl _)). reflexivity.
  - reflexivity.
  - intros d [|n]; unfold FS.up_sub; simpl; auto. f_equal. exact (FS.up_shift amount d (S n)).
Qed.
Definition remove_action replacement depth n :=
  if n =? depth then raw_shift_term replacement depth 0
  else Some (FE.encode_term (FS.Var (if depth <? n then Nat.pred n else n))).
Definition raw_remove_term raw replacement depth := walk_term (remove_action replacement) depth raw.
Definition raw_remove raw replacement depth := walk_formula (remove_action replacement) depth raw.
Lemma remove_action_refines : forall t d n,
  remove_action (FE.encode_term t) d n=Some (FE.encode_term (FS.remove_index t d n)).
Proof.
  intros. unfold remove_action,FS.remove_index. destruct (n=?d); [apply shift_term_refinement | reflexivity].
Qed.
Theorem remove_term_refinement : forall p t d,
  raw_remove_term (FE.encode_term p) (FE.encode_term t) d=Some (FE.encode_term (FS.remove_term p t d)).
Proof.
  intros. unfold raw_remove_term,FS.remove_term. apply (proj1 (walk_term_refines (remove_action (FE.encode_term t)) (FS.remove_index t) (remove_action_refines t))).
Qed.
Theorem remove_formula_refinement : forall p t d,
  raw_remove (FE.encode_formula p) (FE.encode_term t) d=Some (FE.encode_formula (FS.remove p t d)).
Proof.
  intros. unfold raw_remove,FS.remove. apply walk_formula_refines; [apply remove_action_refines | apply FS.up_remove].
Qed.
