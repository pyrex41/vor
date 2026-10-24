From Coq Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

(* An actual first-order stack compiler for the R05 expression constructs.
   Pure scalar literals are opaque atoms; constructor spines use Nil/Cons.
   Calls resolve through one fixed oracle shared by both semantics. *)
Inductive value := Atom (id : nat) | Nil | Cons (head tail : value).
Fixpoint value_size v :=
  match v with Atom _ | Nil => 1 | Cons a b => S (value_size a + value_size b) end.
Fixpoint encode_list vs := match vs with [] => Nil | v::rest => Cons v (encode_list rest) end.
Lemma constructor_field_decreases : forall tag fields v,
  In v fields -> value_size v < value_size (Cons (Atom tag) (encode_list fields)).
Proof.
  intros tag fields. induction fields as [|h fields IH]; intros v IN; simpl in *.
  - contradiction.
  - destruct IN as [EQ|IN]; [subst; lia | specialize (IH _ IN); simpl in IH; lia].
Qed.

Inductive expr :=
| Literal (v : value) | Local (index : nat)
| MakeCons (head tail : expr) | LetIn (value body : expr)
| Invoke (name : nat) (args : exprs)
with exprs := NoArgs | Arg (head : expr) (tail : exprs).
Fixpoint arg_count es := match es with NoArgs => 0 | Arg _ rest => S (arg_count rest) end.

Section Semantics.
Variable call : nat -> list value -> option value.
Inductive evaluates : list value -> expr -> value -> Prop :=
| eval_literal : forall env v, evaluates env (Literal v) v
| eval_local : forall env i v, nth_error env i = Some v -> evaluates env (Local i) v
| eval_cons : forall env a b av bv,
    evaluates env a av -> evaluates env b bv -> evaluates env (MakeCons a b) (Cons av bv)
| eval_let : forall env a b av bv,
    evaluates env a av -> evaluates (av::env) b bv -> evaluates env (LetIn a b) bv
| eval_invoke : forall env name es vs v,
    evaluates_args env es vs -> call name vs = Some v -> evaluates env (Invoke name es) v
with evaluates_args : list value -> exprs -> list value -> Prop :=
| eval_args_nil : forall env, evaluates_args env NoArgs []
| eval_args_cons : forall env e es v vs,
    evaluates env e v -> evaluates_args env es vs -> evaluates_args env (Arg e es) (v::vs).
Scheme evaluates_ind_all := Induction for evaluates Sort Prop
with evaluates_args_ind_all := Induction for evaluates_args Sort Prop.
Combined Scheme evaluation_induction from evaluates_ind_all, evaluates_args_ind_all.

Inductive instruction :=
| Push (v : value) | Get (index : nat) | Join | Enter | Leave
| Call (name arity : nat).
Definition machine := (list value * list value * list (list value))%type.
Definition tick (i : instruction) (s : machine) : option machine :=
  let '(env, stack, frames) := s in
  match i with
  | Push v => Some (env,v::stack,frames)
  | Get n => match nth_error env n with Some v => Some (env,v::stack,frames) | None => None end
  | Join => match stack with b::a::rest => Some (env,Cons a b::rest,frames) | _ => None end
  | Enter => match stack with v::rest => Some (v::env,rest,env::frames) | _ => None end
  | Leave => match frames with old::rest => Some (old,stack,rest) | _ => None end
  | Call name n => if Nat.leb n (length stack) then
      match call name (rev (firstn n stack)) with
      | Some v => Some (env,v::skipn n stack,frames) | None => None end else None
  end.
Fixpoint run (code : list instruction) (s : machine) : option machine :=
  match code with
  | [] => Some s
  | i::rest => match tick i s with Some next => run rest next | None => None end
  end.
Fixpoint compile (e : expr) : list instruction :=
  match e with
  | Literal v => [Push v] | Local i => [Get i]
  | MakeCons a b => compile a ++ compile b ++ [Join]
  | LetIn a b => compile a ++ [Enter] ++ compile b ++ [Leave]
  | Invoke name es => compile_args es ++ [Call name (arg_count es)]
  end
with compile_args (es : exprs) : list instruction :=
  match es with NoArgs => [] | Arg e rest => compile e ++ compile_args rest end.

Lemma run_append : forall first second s,
  run (first ++ second) s =
    match run first s with Some mid => run second mid | None => None end.
Proof.
  induction first as [|i first IH]; intros second s; simpl; auto.
  destruct (tick i s); simpl; auto.
Qed.

Lemma args_length : forall env es vs,
  evaluates_args env es vs -> length vs = arg_count es.
Proof. intros env es vs E; induction E; simpl; auto. Qed.

Lemma invoke_stack : forall name vs v env stack frames,
  call name vs = Some v ->
  tick (Call name (length vs)) (env, rev vs ++ stack, frames) = Some (env,v::stack,frames).
Proof.
  intros. unfold tick. rewrite app_length, rev_length.
  assert (LE: (length vs <=? length vs + length stack) = true) by (apply Nat.leb_le; lia).
  rewrite LE.
  replace (length vs) with (length (rev vs)) by apply rev_length.
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl.
  rewrite app_nil_r, rev_involutive, H.
  rewrite skipn_app, skipn_all, Nat.sub_diag. simpl. reflexivity.
Qed.

Theorem compilation_preserves_evaluation :
  (forall env e v, evaluates env e v -> forall stack frames,
    run (compile e) (env,stack,frames) = Some (env,v::stack,frames)) /\
  (forall env es vs, evaluates_args env es vs -> forall stack frames,
    run (compile_args es) (env,stack,frames) = Some (env,rev vs ++ stack,frames)).
Proof.
  apply evaluation_induction; intros; simpl.
  - reflexivity.
  - rewrite e. reflexivity.
  - rewrite run_append, H, run_append, H0. reflexivity.
  - rewrite run_append, H. simpl. rewrite run_append, H0. reflexivity.
  - rewrite run_append, H.
    assert (L: length vs = arg_count es) by (eapply args_length; eauto).
    rewrite <- L.
    change (match tick (Call name (length vs)) (env,rev vs ++ stack,frames) with
      | Some result => Some result | None => None end = Some (env,v::stack,frames)).
    rewrite (invoke_stack env stack frames e0). reflexivity.
  - reflexivity.
  - rewrite run_append, H, H0. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Corollary compiled_result_exact : forall env e v,
  evaluates env e v -> run (compile e) (env,[],[]) = Some (env,[v],[]).
Proof. intros. apply (proj1 compilation_preserves_evaluation); auto. Qed.

(* A forward theorem plus source totality suffices for all successful target
   executions: the target evaluator is a function, so it cannot return another
   result. There is no hidden premise that the target returned a safe value. *)
Corollary compiled_total_and_all_outcomes : forall env e,
  (exists v, evaluates env e v) ->
  (exists v, run (compile e) (env,[],[]) = Some (env,[v],[])) /\
  (forall result, run (compile e) (env,[],[]) = Some result ->
    exists v, result = (env,[v],[]) /\ evaluates env e v).
Proof.
  intros env e [v E]. pose proof (compiled_result_exact E) as R.
  split; [eauto | intros result K; rewrite R in K; inversion K; subst; eauto].
Qed.
End Semantics.
