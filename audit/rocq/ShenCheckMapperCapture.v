From Coq Require Import List.
From VorAudit Require Import NativeLookup.
Import ListNotations.
(* Exact ps capture digest: b316f0c0380b6549988e901a2ef7a977f8a903b78737a2f3b0fd6faa2f134790 *)
Definition actual_shencheck_mapper_kl : datum := (Cell (Sym 0) (Cell (Sym 1) (Cell (Cell (Sym 17) Nil) (Cell (Cell (Sym 2) (Cell (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Sym 17) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 16) (Cell (Cell (Sym 7) (Cell (Sym 17) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 9) (Cell (Cell (Sym 7) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 10) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) (Cell (Cell (Sym 6) (Cell (Sym 13) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 17) (Cell Nil Nil))) (Cell Nil Nil))) Nil))) Nil)) (Cell (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Sym 17) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 16) (Cell (Cell (Sym 7) (Cell (Sym 17) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 9) (Cell (Cell (Sym 7) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 11) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) (Cell (Cell (Sym 6) (Cell (Sym 13) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 17) (Cell Nil Nil))) (Cell Nil Nil))) Nil))) Nil)) (Cell (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Sym 17) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 16) (Cell (Cell (Sym 7) (Cell (Sym 17) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 9) (Cell (Cell (Sym 7) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell (Sym 12) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 3) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil)) Nil)) Nil))) (Cell (Cell (Sym 5) (Cell Nil (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) Nil)) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) Nil))) (Cell (Cell (Sym 6) (Cell (Sym 13) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 16) (Cell (Cell (Sym 6) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) (Cell (Cell (Sym 6) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 9) (Cell (Cell (Sym 6) (Cell (Sym 10) (Cell Nil Nil))) Nil))) (Cell Nil Nil))) Nil))) Nil))) Nil))) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 16) (Cell (Cell (Sym 6) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) (Cell (Cell (Sym 6) (Cell (Cell (Sym 7) (Cell (Cell (Sym 8) (Cell (Cell (Sym 8) (Cell (Sym 17) Nil)) Nil)) Nil)) (Cell (Cell (Sym 6) (Cell (Cell (Sym 6) (Cell (Sym 9) (Cell (Cell (Sym 6) (Cell (Sym 11) (Cell Nil Nil))) Nil))) (Cell Nil Nil))) Nil))) Nil))) Nil))) (Cell Nil Nil))) Nil))) (Cell Nil Nil))) Nil))) Nil)) (Cell (Cell (Boolean true) (Cell (Cell (Sym 6) (Cell (Sym 14) (Cell (Cell (Sym 6) (Cell (Sym 15) (Cell Nil Nil))) Nil))) Nil)) Nil))))) Nil)))).
(* MAPPER_PROOF_BEGIN *)
(* The fixed primitive IDs match NativeLookup: cond=2, and=3, cons?=4,
   equal=5, cons=6, hd=7, tl=8. Name-to-slot resolution is performed in
   Rocq by this decoder; the capture exporter cannot choose a local slot. *)
Definition decode_definition_one (raw : datum) : option expr :=
  match raw with
  | Cell (Sym 0) (Cell (Sym 1) (Cell (Cell (Sym x) Nil) (Cell body Nil))) =>
      decode_expr [x] body
  | _ => None
  end.

Lemma shencheck_mapper_capture_shape :
  exists body, decode_definition_one actual_shencheck_mapper_kl = Some body.
Proof. eexists. vm_compute. reflexivity. Qed.

Definition shencheck_mapper_body : expr :=
  match decode_definition_one actual_shencheck_mapper_kl with
  | Some body => body | None => Fail
  end.

Theorem shencheck_mapper_deterministic : forall env e a b,
  eval shencheck_mapper_body env e a ->
  eval shencheck_mapper_body env e b -> a = b.
Proof. intros. eapply eval_deterministic; eauto. Qed.

(* Canonical inert encodings of the three mapper inputs and outputs. The
   constructor and primitive IDs are those in the captured dictionary above. *)
Definition obs (identity payload effect : datum) : datum :=
  Cell (Sym 16) (Cell identity (Cell payload
    (Cell (Cell (Sym 9) (Cell effect Nil)) Nil))).
Definition poss1 (x : datum) : datum := Cell (Sym 13) (Cell (Cell x Nil) Nil).
Definition poss2 (x y : datum) : datum :=
  Cell (Sym 13) (Cell (Cell x (Cell y Nil)) Nil).
Definition applied_tag := Sym 10.
Definition not_applied_tag := Sym 11.
Definition unknown_tag := Sym 12.

Ltac mapper_eval :=
  repeat match goal with
  | |- eval _ _ (And _ _) _ => eapply eval_and_true
  | |- eval _ _ (Unary _ _) _ => eapply eval_unary
  | |- eval _ _ (Binary _ _ _) _ => eapply eval_binary
  | |- eval _ _ (Local _) _ => eapply eval_local; cbn; reflexivity
  | |- eval _ _ (Lit _) _ => eapply eval_lit
  end; cbn; eauto.

Ltac mapper_false_cond :=
  eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_true; [mapper_eval|]
  ; eapply eval_and_false; mapper_eval.

Lemma shencheck_mapper_applied_eval : forall identity payload,
  eval shencheck_mapper_body [obs identity payload applied_tag] shencheck_mapper_body
    (poss1 (obs identity payload applied_tag)).
Proof. intros. cbn [shencheck_mapper_body shencheck_mapper_body
  decode_definition_one decode_expr decode_cond obs poss1 applied_tag].
  repeat (econstructor; cbn); eauto. Qed.

Lemma shencheck_mapper_not_applied_eval : forall identity payload,
  eval shencheck_mapper_body [obs identity payload not_applied_tag] shencheck_mapper_body
    (poss1 (obs identity payload not_applied_tag)).
Proof. intros. cbn [shencheck_mapper_body decode_definition_one decode_expr
  decode_cond obs poss1 not_applied_tag].
  unfold not_applied_tag.
  eapply eval_if_false.
  - mapper_false_cond.
  - eapply eval_if_true; [mapper_eval|].
    repeat (econstructor; cbn); eauto. Qed.

Lemma shencheck_mapper_unknown_eval : forall identity payload,
  eval shencheck_mapper_body [obs identity payload unknown_tag] shencheck_mapper_body
    (poss2 (obs identity payload applied_tag)
      (obs identity payload not_applied_tag)).
Proof. intros. cbn [shencheck_mapper_body decode_definition_one decode_expr
  decode_cond obs poss1 poss2 applied_tag not_applied_tag unknown_tag].
  unfold unknown_tag, applied_tag, not_applied_tag.
  eapply eval_if_false.
  - mapper_false_cond.
  - eapply eval_if_false.
    + mapper_false_cond.
    + eapply eval_if_true; [mapper_eval|].
      repeat (econstructor; cbn); eauto. Qed.

Theorem shencheck_mapper_output_spec : forall identity payload effect result,
  (effect = applied_tag \/ effect = not_applied_tag \/ effect = unknown_tag) ->
  eval shencheck_mapper_body [obs identity payload effect] shencheck_mapper_body result ->
  result = poss1 (obs identity payload applied_tag) \/
  result = poss1 (obs identity payload not_applied_tag) \/
  result = poss2 (obs identity payload applied_tag)
                    (obs identity payload not_applied_tag).
Proof.
  intros identity payload effect result H E.
  destruct H as [Ha|Hn].
  - subst effect. left. symmetry.
    eapply (@eval_deterministic shencheck_mapper_body
      [obs identity payload applied_tag] shencheck_mapper_body
      (poss1 (obs identity payload applied_tag))).
    + apply shencheck_mapper_applied_eval.
    + exact E.
  - destruct Hn as [Hna|Hu].
    + subst effect. right; left. symmetry.
      eapply (@eval_deterministic shencheck_mapper_body
        [obs identity payload not_applied_tag] shencheck_mapper_body
        (poss1 (obs identity payload not_applied_tag))).
      * apply shencheck_mapper_not_applied_eval.
      * exact E.
    + subst effect. right; right. symmetry.
      eapply (@eval_deterministic shencheck_mapper_body
        [obs identity payload unknown_tag] shencheck_mapper_body
        (poss2 (obs identity payload applied_tag)
          (obs identity payload not_applied_tag))).
      * apply shencheck_mapper_unknown_eval.
      * exact E.
Qed.

Corollary shencheck_mapper_applied_all_outcomes : forall identity payload result,
  eval shencheck_mapper_body [obs identity payload applied_tag]
    shencheck_mapper_body result ->
  result = poss1 (obs identity payload applied_tag).
Proof.
  intros. symmetry.
  eapply (@eval_deterministic shencheck_mapper_body
    [obs identity payload applied_tag] shencheck_mapper_body
    (poss1 (obs identity payload applied_tag))).
  - apply shencheck_mapper_applied_eval.
  - exact H.
Qed.

Corollary shencheck_mapper_not_applied_all_outcomes : forall identity payload result,
  eval shencheck_mapper_body [obs identity payload not_applied_tag]
    shencheck_mapper_body result ->
  result = poss1 (obs identity payload not_applied_tag).
Proof.
  intros. symmetry.
  eapply (@eval_deterministic shencheck_mapper_body
    [obs identity payload not_applied_tag] shencheck_mapper_body
    (poss1 (obs identity payload not_applied_tag))).
  - apply shencheck_mapper_not_applied_eval.
  - exact H.
Qed.

Corollary shencheck_mapper_unknown_all_outcomes : forall identity payload result,
  eval shencheck_mapper_body [obs identity payload unknown_tag]
    shencheck_mapper_body result ->
  result = poss2 (obs identity payload applied_tag)
                    (obs identity payload not_applied_tag).
Proof.
  intros. symmetry.
  eapply (@eval_deterministic shencheck_mapper_body
    [obs identity payload unknown_tag] shencheck_mapper_body
    (poss2 (obs identity payload applied_tag)
      (obs identity payload not_applied_tag))).
  - apply shencheck_mapper_unknown_eval.
  - exact H.
Qed.
