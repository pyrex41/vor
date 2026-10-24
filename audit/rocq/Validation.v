From Coq Require Import List Arith.
From VorAudit Require Import Compiler.
Import ListNotations.
Set Implicit Arguments.

Definition value_eq_dec : forall a b : value, {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition instruction_eq_dec : forall a b : instruction, {a=b}+{a<>b}.
Proof. decide equality; try apply Nat.eq_dec; apply value_eq_dec. Defined.
Definition expect i code :=
  match code with j::rest => if instruction_eq_dec j i then Some rest else None | [] => None end.
Fixpoint validate (e : expr) (code : list instruction) : option (list instruction) :=
  match e with
  | Literal v => expect (Push v) code
  | Local i => expect (Get i) code
  | MakeCons a b =>
    match validate a code with Some mid =>
      match validate b mid with Some tail => expect Join tail | None => None end
    | None => None end
  | LetIn a b =>
    match validate a code with Some mid =>
      match expect Enter mid with Some next =>
        match validate b next with Some tail => expect Leave tail | None => None end
      | None => None end
    | None => None end
  | Invoke f es => match validate_args es code with
      Some tail => expect (Call f (arg_count es)) tail | None => None end
  end
with validate_args (es : exprs) (code : list instruction) : option (list instruction) :=
  match es with
  | NoArgs => Some code
  | Arg e rest => match validate e code with Some mid => validate_args rest mid | None => None end
  end.
Lemma expect_sound : forall i code rest,
  expect i code = Some rest -> code = i :: rest.
Proof.
  intros i [|j code] rest H; simpl in H; try discriminate.
  destruct (instruction_eq_dec j i); try discriminate. inversion H; subst; reflexivity.
Qed.
Scheme expr_ind_all := Induction for expr Sort Prop
with exprs_ind_all := Induction for exprs Sort Prop.
Combined Scheme syntax_induction from expr_ind_all, exprs_ind_all.

Theorem validation_exact :
  (forall e code rest, validate e code = Some rest -> code = compile e ++ rest) /\
  (forall es code rest, validate_args es code = Some rest -> code = compile_args es ++ rest).
Proof.
  apply syntax_induction.
  - intros v code rest CHECK. simpl in CHECK. apply expect_sound in CHECK. exact CHECK.
  - intros i code rest CHECK. simpl in CHECK. apply expect_sound in CHECK. exact CHECK.
  - intros a IHa b IHb code rest CHECK. simpl in *.
    destruct (validate a code) as [mid|] eqn:A; try discriminate.
    destruct (validate b mid) as [tail|] eqn:B; try discriminate.
    apply IHa in A. apply IHb in B. apply expect_sound in CHECK.
    subst code mid tail. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
  - intros a IHa b IHb code rest CHECK. simpl in *.
    destruct (validate a code) as [mid|] eqn:A; try discriminate.
    destruct (expect Enter mid) as [next|] eqn:B; try discriminate.
    destruct (validate b next) as [tail|] eqn:C; try discriminate.
    apply IHa in A. apply expect_sound in B. apply IHb in C. apply expect_sound in CHECK.
    subst code mid next tail. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
  - intros name es IH code rest CHECK. simpl in *.
    destruct (validate_args es code) as [mid|] eqn:A; try discriminate.
    apply IH in A. apply expect_sound in CHECK. subst code mid. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
  - intros code rest CHECK. inversion CHECK; reflexivity.
  - intros a IHa es IHb code rest CHECK. simpl in *.
    destruct (validate a code) as [mid|] eqn:A; try discriminate.
    apply IHa in A. apply IHb in CHECK. subst code mid. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. reflexivity.
Qed.

Theorem checked_compilation_preserves : forall call env e code v,
  validate e code = Some [] -> evaluates call env e v ->
  run call code (env,[],[]) = Some (env,[v],[]).
Proof.
  intros. apply (proj1 validation_exact) in H. rewrite app_nil_r in H. subst code.
  eapply compiled_result_exact; eauto.
Qed.

Theorem checked_compilation_total_and_all_outcomes : forall call env e code,
  validate e code = Some [] -> (exists v, evaluates call env e v) ->
  (exists v, run call code (env,[],[]) = Some (env,[v],[])) /\
  (forall result, run call code (env,[],[]) = Some result ->
    exists v, result = (env,[v],[]) /\ evaluates call env e v).
Proof.
  intros. apply (proj1 validation_exact) in H. rewrite app_nil_r in H. subst code.
  eapply compiled_total_and_all_outcomes; eauto.
Qed.
