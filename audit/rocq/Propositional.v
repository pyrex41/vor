From Coq Require Import List Arith Lia.
From VorAudit Require Import Checker.
Import ListNotations.
Set Implicit Arguments.

(* The quantifier-free constructive rule family of kernel/proof.shen.
   Atom identifiers stand for zero-arity predicates; no classical oracle. *)
Inductive formula :=
| Atom (id : nat) | Top | Bottom
| Both (p q : formula) | Either (p q : formula) | Impl (p q : formula).
Definition formula_eq_dec : forall p q : formula, {p=q}+{p<>q}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Inductive proof :=
| Hyp (index : nat) | Unit | Pair (a b : proof)
| Fst (other : formula) (a : proof) | Snd (other : formula) (a : proof)
| Intro (a : proof) | Apply (antecedent : formula) (a b : proof)
| Inl (a : proof) | Inr (a : proof)
| Cases (p q : formula) (sum left right : proof) | Exfalso (a : proof).
Record goal := G { context : list formula; target : formula; evidence : proof }.
Definition expand (g : goal) : option (list goal) :=
  let '(G gamma p e) := g in
  match e with
  | Hyp n => match nth_error gamma n with
             | Some q => if formula_eq_dec q p then Some [] else None
             | None => None end
  | Unit => match p with Top => Some [] | _ => None end
  | Pair a b => match p with Both l r => Some [G gamma l a; G gamma r b] | _ => None end
  | Fst q a => Some [G gamma (Both p q) a]
  | Snd q a => Some [G gamma (Both q p) a]
  | Intro a => match p with Impl l r => Some [G (l::gamma) r a] | _ => None end
  | Apply q a b => Some [G gamma (Impl q p) a; G gamma q b]
  | Inl a => match p with Either l r => Some [G gamma l a] | _ => None end
  | Inr a => match p with Either l r => Some [G gamma r a] | _ => None end
  | Cases l r e a b => Some [G gamma (Either l r) e; G (l::gamma) p a; G (r::gamma) p b]
  | Exfalso a => Some [G gamma Bottom a]
  end.
Fixpoint denote (rho : nat -> Prop) (p : formula) : Prop :=
  match p with
  | Atom n => rho n | Top => True | Bottom => False
  | Both p q => denote rho p /\ denote rho q
  | Either p q => denote rho p \/ denote rho q
  | Impl p q => denote rho p -> denote rho q
  end.
Definition valid (g : goal) := forall rho,
  (forall p, In p (context g) -> denote rho p) -> denote rho (target g).

Ltac premises :=
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  | H : Forall _ [] |- _ => clear H
  end.

Theorem expand_sound : forall g ps,
  expand g = Some ps -> Forall valid ps -> valid g.
Proof.
  intros [gamma p e] ps E H. destruct e; simpl in E.
  - destruct (nth_error gamma index) as [q|] eqn:N; try discriminate.
    destruct (formula_eq_dec q p); try discriminate. subst q.
    unfold valid; simpl. intros rho HG. apply HG.
    eapply nth_error_In; eauto.
  - destruct p; try discriminate. unfold valid; simpl; auto.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. firstorder.
  - inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. intros rho HG HP.
    apply H2 with (rho := rho). intros r [EQ|IN]; [subst r; exact HP | apply HG; exact IN].
  - inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. firstorder.
  - destruct p; try discriminate. inversion E; subst. premises.
    unfold valid in *; simpl in *. firstorder.
  - inversion E; subst. premises. unfold valid in *; simpl in *.
    intros rho HG. destruct (H2 rho HG) as [HL|HR].
    + apply H1 with (rho := rho). intros r [EQ|IN]; [subst r; exact HL | apply HG; exact IN].
    + apply H3 with (rho := rho). intros r [EQ|IN]; [subst r; exact HR | apply HG; exact IN].
  - inversion E; subst. premises. unfold valid in *; simpl in *. firstorder.
Qed.

Theorem checker_sound : forall fuel gamma p e rem,
  check expand fuel [G gamma p e] = Some rem -> valid (G gamma p e).
Proof.
  intros. pose proof (@check_sound goal expand valid expand_sound _ _ _ H) as V.
  inversion V; auto.
Qed.

Theorem closed_bottom_rejected : forall fuel e rem,
  check expand fuel [G [] Bottom e] <> Some rem.
Proof.
  intros fuel e rem H. apply checker_sound in H.
  unfold valid in H; simpl in H. apply (H (fun _ => False)).
  intros p HP. inversion HP.
Qed.
