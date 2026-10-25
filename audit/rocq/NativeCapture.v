From Coq Require Import List.
From VorAudit Require Import NativeLookup.
Import ListNotations.
(* Injectively encoded capture, modulo fresh parameter names: 5b23cc4a6d8a375cb4011410a9eb41669221d679b89dd7bbc4509ae6b2ebf547 *)
Definition actual_lookup_kl : datum := (Cell (Sym 0) (Cell (Sym 1) (Cell (Cell (Sym 13) (Cell (Sym 14) Nil)) (Cell (Cell (Sym 2) (Cell (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Sym 13) Nil)) (Cell (Cell (Sym 5) (Cell (Num 0) (Cell (Sym 14) Nil))) Nil))) (Cell (Cell (Sym 6) (Cell (Sym 11) (Cell (Cell (Sym 6) (Cell (Cell (Sym 7) (Cell (Sym 13) Nil)) (Cell Nil Nil))) Nil))) Nil)) (Cell (Cell (Cell (Sym 3) (Cell (Cell (Sym 4) (Cell (Sym 13) Nil)) (Cell (Cell (Sym 9) (Cell (Sym 14) (Cell (Num 0) Nil))) Nil))) (Cell (Cell (Sym 1) (Cell (Cell (Sym 8) (Cell (Sym 13) Nil)) (Cell (Cell (Sym 10) (Cell (Sym 14) (Cell (Num 1) Nil))) Nil))) Nil)) (Cell (Cell (Boolean true) (Cell (Sym 12) Nil)) Nil)))) Nil)))).
Lemma actual_lookup_decoded : decode_definition actual_lookup_kl = Some lookup_body.
Proof. vm_compute. reflexivity. Qed.
Theorem actual_lookup_total : forall body xs n,
  decode_definition actual_lookup_kl = Some body ->
  eval body [encode_list xs; Num n] body (lookup_result xs n).
Proof. intros. rewrite actual_lookup_decoded in H. inversion H; subst. apply native_lookup_total. Qed.
Theorem actual_lookup_all_outcomes : forall body xs n v,
  decode_definition actual_lookup_kl = Some body ->
  eval body [encode_list xs; Num n] body v -> v=lookup_result xs n.
Proof. intros. rewrite actual_lookup_decoded in H. inversion H; subst. eapply native_lookup_all_outcomes; eauto. Qed.
