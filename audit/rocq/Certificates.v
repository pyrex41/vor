From Coq Require Import List.
From VorAudit Require Import Compiler Validation.
Import ListNotations.
(* Exact fixture bytes SHA-256: 9ecc3aef916976b0e6c0c192b98b5305cbe3a78bcde459625141786379ad2742 *)
(* Distinct scalar classes/names map injectively to opaque atoms. *)
Definition body_0_0 : expr := (Local 0).
Definition body_0_0_code : list instruction := [(Get 0)].
Lemma body_0_0_certificate : validate body_0_0 body_0_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_0_0_preserves : forall call env v, evaluates call env body_0_0 v ->
  run call body_0_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_0_0_certificate | eassumption]. Qed.
Definition body_0_1 : expr := (MakeCons (Literal (Atom 30)) (MakeCons (Invoke 31 (Arg (Local 0) (Arg (Local 1) NoArgs))) (Literal Nil))).
Definition body_0_1_code : list instruction := [(Push (Atom 30)); (Get 0); (Get 1); (Call 31 2); (Push Nil); Join; Join].
Lemma body_0_1_certificate : validate body_0_1 body_0_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_0_1_preserves : forall call env v, evaluates call env body_0_1 v ->
  run call body_0_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_0_1_certificate | eassumption]. Qed.
Definition body_1_0 : expr := (Literal (Atom 40)).
Definition body_1_0_code : list instruction := [(Push (Atom 40))].
Lemma body_1_0_certificate : validate body_1_0 body_1_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_1_0_preserves : forall call env v, evaluates call env body_1_0 v ->
  run call body_1_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_1_0_certificate | eassumption]. Qed.
Definition body_1_1 : expr := (MakeCons (Literal (Atom 30)) (MakeCons (Invoke 33 (Arg (Local 0) NoArgs)) (Literal Nil))).
Definition body_1_1_code : list instruction := [(Push (Atom 30)); (Get 0); (Call 33 1); (Push Nil); Join; Join].
Lemma body_1_1_certificate : validate body_1_1 body_1_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_1_1_preserves : forall call env v, evaluates call env body_1_1 v ->
  run call body_1_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_1_1_certificate | eassumption]. Qed.
Definition body_2_0 : expr := (Invoke 31 (Arg (Literal (Atom 40)) (Arg (Literal (Atom 40)) NoArgs))).
Definition body_2_0_code : list instruction := [(Push (Atom 40)); (Push (Atom 40)); (Call 31 2)].
Lemma body_2_0_certificate : validate body_2_0 body_2_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_2_0_preserves : forall call env v, evaluates call env body_2_0 v ->
  run call body_2_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_2_0_certificate | eassumption]. Qed.
Definition body_2_1 : expr := (LetIn (Invoke 33 (Arg (MakeCons (Literal (Atom 30)) (MakeCons (Local 0) (Literal Nil))) NoArgs)) (Invoke 31 (Arg (Local 0) (Arg (Local 0) NoArgs)))).
Definition body_2_1_code : list instruction := [(Push (Atom 30)); (Get 0); (Push Nil); Join; Join; (Call 33 1); Enter; (Get 0); (Get 0); (Call 31 2); Leave].
Lemma body_2_1_certificate : validate body_2_1 body_2_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_2_1_preserves : forall call env v, evaluates call env body_2_1 v ->
  run call body_2_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_2_1_certificate | eassumption]. Qed.
Definition body_3_0 : expr := (Literal (Atom 40)).
Definition body_3_0_code : list instruction := [(Push (Atom 40))].
Lemma body_3_0_certificate : validate body_3_0 body_3_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_3_0_preserves : forall call env v, evaluates call env body_3_0 v ->
  run call body_3_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_3_0_certificate | eassumption]. Qed.
Definition body_3_1 : expr := (MakeCons (Literal (Atom 30)) (MakeCons (Invoke 34 (Arg (Local 1) NoArgs)) (Literal Nil))).
Definition body_3_1_code : list instruction := [(Push (Atom 30)); (Get 1); (Call 34 1); (Push Nil); Join; Join].
Lemma body_3_1_certificate : validate body_3_1 body_3_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_3_1_preserves : forall call env v, evaluates call env body_3_1 v ->
  run call body_3_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_3_1_certificate | eassumption]. Qed.
Definition body_4_0 : expr := (Local 0).
Definition body_4_0_code : list instruction := [(Get 0)].
Lemma body_4_0_certificate : validate body_4_0 body_4_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_4_0_preserves : forall call env v, evaluates call env body_4_0 v ->
  run call body_4_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_4_0_certificate | eassumption]. Qed.
Definition body_4_1 : expr := (MakeCons (Literal (Atom 11)) (MakeCons (Local 0) (MakeCons (Invoke 32 (Arg (Local 1) (Arg (Local 2) NoArgs))) (Literal Nil)))).
Definition body_4_1_code : list instruction := [(Push (Atom 11)); (Get 0); (Get 1); (Get 2); (Call 32 2); (Push Nil); Join; Join; Join].
Lemma body_4_1_certificate : validate body_4_1 body_4_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_4_1_preserves : forall call env v, evaluates call env body_4_1 v ->
  run call body_4_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_4_1_certificate | eassumption]. Qed.
Definition body_5_0 : expr := (Local 0).
Definition body_5_0_code : list instruction := [(Get 0)].
Lemma body_5_0_certificate : validate body_5_0 body_5_0_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_5_0_preserves : forall call env v, evaluates call env body_5_0 v ->
  run call body_5_0_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_5_0_certificate | eassumption]. Qed.
Definition body_5_1 : expr := (Invoke 35 (Arg (Local 1) (Arg (MakeCons (Literal (Atom 11)) (MakeCons (Local 0) (MakeCons (Local 2) (Literal Nil)))) NoArgs))).
Definition body_5_1_code : list instruction := [(Get 1); (Push (Atom 11)); (Get 0); (Get 2); (Push Nil); Join; Join; Join; (Call 35 2)].
Lemma body_5_1_certificate : validate body_5_1 body_5_1_code = Some [].
Proof. vm_compute. reflexivity. Qed.
Theorem body_5_1_preserves : forall call env v, evaluates call env body_5_1 v ->
  run call body_5_1_code (env, [], []) = Some (env, [v], []).
Proof. intros. eapply checked_compilation_preserves; [exact body_5_1_certificate | eassumption]. Qed.
(* 12 symbolic-body certificates; each theorem quantifies over all environments and call interpretations. *)
