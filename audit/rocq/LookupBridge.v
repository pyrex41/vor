From Coq Require Import List.
From VorAudit Require Import NativeLookup NativeCapture FirstOrderSyntax FirstOrderSemantics.
Import ListNotations.
Set Implicit Arguments.
Module NV := NativeLookup.
Module FS := FirstOrderSyntax.
Module FM := FirstOrderSemantics.

(* The evaluated body is obtained from the ACTUAL exported KLambda definition,
   not a caller's implementation oracle or a different hand-written function. *)
Definition captured_body := match NV.decode_definition NativeCapture.actual_lookup_kl with
  | Some body=>body | None=>NV.Fail end.
Lemma captured_body_exact : captured_body=NV.lookup_body.
Proof. unfold captured_body. rewrite NativeCapture.actual_lookup_decoded. reflexivity. Qed.
Definition found_sort (encode_sort:nat->NV.datum) s := NV.Cell (NV.Sym 11) (NV.Cell (encode_sort s) NV.Nil).
Definition native_sort_result encode_sort result := match result with
  | Some s=>found_sort encode_sort s | None=>NV.Sym 12 end.
Theorem native_variable_lookup_correspondence : forall encode_sort sig vars n,
  NV.eval captured_body [NV.encode_list (map encode_sort vars);NV.Num n] captured_body
    (native_sort_result encode_sort (FM.term_sort sig vars (FS.Var n))).
Proof.
  intros. rewrite captured_body_exact. pose proof (NV.native_lookup_total (map encode_sort vars) n) as E.
  unfold NV.lookup_result in E. rewrite nth_error_map in E. simpl.
  destruct (nth_error vars n); exact E.
Qed.
Theorem native_variable_lookup_all_outcomes : forall encode_sort sig vars n value,
  NV.eval captured_body [NV.encode_list (map encode_sort vars);NV.Num n] captured_body value ->
  value=native_sort_result encode_sort (FM.term_sort sig vars (FS.Var n)).
Proof.
  intros. eapply NV.eval_deterministic; [exact H | apply native_variable_lookup_correspondence].
Qed.
Theorem native_variable_found_iff : forall encode_sort, (forall a b,encode_sort a=encode_sort b -> a=b) -> forall sig vars n s,
  NV.eval captured_body [NV.encode_list (map encode_sort vars);NV.Num n] captured_body (found_sort encode_sort s)
  <-> FM.term_sort sig vars (FS.Var n)=Some s.
Proof.
  intros encode_sort INJECT sig vars n s; split; intro H.
  - apply (native_variable_lookup_all_outcomes encode_sort sig vars) in H. simpl in H.
    change (nth_error vars n=Some s). destruct (nth_error vars n); inversion H.
    f_equal. apply INJECT. symmetry; assumption.
  - pose proof (native_variable_lookup_correspondence encode_sort sig vars n) as E. rewrite H in E. exact E.
Qed.
