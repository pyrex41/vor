From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Set Implicit Arguments.

(* Pure KLambda operations used by the ACTUAL ps-export of vor.fol-at.
   No opaque call oracle. Recursion invokes the exact captured function body. *)
Inductive datum := Nil | Cell (a b:datum) | Sym (id:nat) | Num (n:nat) | Boolean (b:bool) | Text (id:nat) | BadNumber (id:nat).
Fixpoint datum_eq_dec (a b:datum) : {a=b}+{a<>b}.
Proof. decide equality; try apply Bool.bool_dec; apply Nat.eq_dec. Defined.
Inductive unary := IsCons | Head | Tail.
Inductive binary := Equal | Greater | Subtract | MakeCons.
Inductive expr := Lit (v:datum) | Local (n:nat)
| Unary (op:unary) (a:expr) | Binary (op:binary) (a b:expr)
| If (a b c:expr) | And (a b:expr) | Recur (a b:expr) | Fail.
Definition unary_value op v :=
  match op,v with
  | IsCons,Cell _ _ => Some (Boolean true)
  | IsCons,_ => Some (Boolean false)
  | Head,Cell a _ => Some a | Tail,Cell _ b => Some b | _,_ => None end.
Definition binary_value op a b :=
  match op,a,b with
  | Equal,a,b => Some (Boolean (if datum_eq_dec a b then true else false))
  | Greater,Num a,Num b => Some (Boolean (b <? a))
  | Subtract,Num a,Num b => if b <=? a then Some (Num (a-b)) else None
  | MakeCons,a,b => Some (Cell a b)
  | _,_,_ => None end.
Definition lookup_body :=
  If (And (Unary IsCons (Local 0)) (Binary Equal (Lit (Num 0)) (Local 1)))
    (Binary MakeCons (Lit (Sym 11)) (Binary MakeCons (Unary Head (Local 0)) (Lit Nil)))
    (If (And (Unary IsCons (Local 0)) (Binary Greater (Local 1) (Lit (Num 0))))
      (Recur (Unary Tail (Local 0)) (Binary Subtract (Local 1) (Lit (Num 1))))
      (If (Lit (Boolean true)) (Lit (Sym 12)) Fail)).
Section Evaluation.
Variable body:expr.
Inductive eval : list datum -> expr -> datum -> Prop :=
| eval_lit : forall env v, eval env (Lit v) v
| eval_local : forall env n v, nth_error env n=Some v -> eval env (Local n) v
| eval_unary : forall env op a v result,
    eval env a v -> unary_value op v=Some result -> eval env (Unary op a) result
| eval_binary : forall env op a b av bv result,
    eval env a av -> eval env b bv -> binary_value op av bv=Some result -> eval env (Binary op a b) result
| eval_if_true : forall env a b c v, eval env a (Boolean true) -> eval env b v -> eval env (If a b c) v
| eval_if_false : forall env a b c v, eval env a (Boolean false) -> eval env c v -> eval env (If a b c) v
| eval_and_false : forall env a b, eval env a (Boolean false) -> eval env (And a b) (Boolean false)
| eval_and_true : forall env a b v, eval env a (Boolean true) -> eval env b (Boolean v) -> eval env (And a b) (Boolean v)
| eval_recur : forall env a b av bv v,
    eval env a av -> eval env b bv -> eval [av;bv] body v -> eval env (Recur a b) v.
End Evaluation.
Fixpoint encode_list xs := match xs with []=>Nil | x::xs=>Cell x (encode_list xs) end.
Definition lookup_result xs n := match nth_error xs n with
  Some x=>Cell (Sym 11) (Cell x Nil) | None=>Sym 12 end.

Ltac atom_eval := first [apply eval_lit | apply eval_local; reflexivity].
Ltac primitive_eval := first
 [atom_eval | eapply eval_unary; [atom_eval|reflexivity]
 | eapply eval_binary; [atom_eval|atom_eval|reflexivity]].
Theorem native_lookup_total : forall xs n,
  eval lookup_body [encode_list xs;Num n] lookup_body (lookup_result xs n).
Proof.
  induction xs as [|h xs IH]; intros n.
  - unfold lookup_body at 2. apply eval_if_false.
    + apply eval_and_false. primitive_eval.
    + apply eval_if_false; [apply eval_and_false; primitive_eval |].
      destruct n; simpl; apply eval_if_true; apply eval_lit.
  - destruct n as [|n].
    + unfold lookup_body at 2. apply eval_if_true.
      * apply eval_and_true; primitive_eval.
      * eapply eval_binary.
        -- apply eval_lit.
        -- eapply eval_binary; [primitive_eval | apply eval_lit | reflexivity].
        -- reflexivity.
    + unfold lookup_body at 2. apply eval_if_false.
      * apply eval_and_true; primitive_eval.
      * apply eval_if_true.
        -- apply eval_and_true; primitive_eval.
        -- eapply eval_recur.
           ++ primitive_eval.
           ++ eapply eval_binary; [atom_eval | atom_eval | simpl; rewrite Nat.sub_0_r; reflexivity].
           ++ apply IH.
Qed.

(* Generic determinism: covers arbitrary finite evaluations and recursive calls,
   not only the particular input used by the totality induction. *)
Theorem eval_deterministic : forall body env e a,
  eval body env e a -> forall b, eval body env e b -> a=b.
Proof.
  intros body env e a H. induction H; intros output E; inversion E; subst;
    try reflexivity;
    repeat match goal with
    | H: forall b, eval _ ?env ?e b -> _ = b, K:eval _ ?env ?e _ |- _ =>
        specialize (H _ K); inversion H; subst; clear H
    end; try congruence; auto.
Qed.
Corollary native_lookup_all_outcomes : forall xs n v,
  eval lookup_body [encode_list xs;Num n] lookup_body v -> v=lookup_result xs n.
Proof. intros. symmetry. eapply eval_deterministic; [apply native_lookup_total | eauto]. Qed.

(* The capture is raw KLambda data. Name-to-slot resolution is performed and
   checked INSIDE Rocq; the serializer does not get to invent local indices.
   Reserved symbol IDs 0..12 are listed in the capture-format documentation. *)
Fixpoint local_index name params : option nat :=
  match params with []=>None | p::ps=>if name =? p then Some 0 else option_map S (local_index name ps) end.
Fixpoint decode_expr params raw : option expr :=
  match raw with
  | Nil => Some (Lit Nil) | Num n=>Some (Lit (Num n)) | Boolean b=>Some (Lit (Boolean b))
  | Sym n=> match local_index n params with Some i=>Some (Local i) | None=>Some (Lit (Sym n)) end
  | Cell (Sym 2) cases => decode_cond params cases
  | Cell (Sym op) (Cell a Nil) =>
      match decode_expr params a with
      | Some a => match op with 4=>Some (Unary IsCons a) | 7=>Some (Unary Head a) | 8=>Some (Unary Tail a) | _=>None end
      | None=>None end
  | Cell (Sym op) (Cell a (Cell b Nil)) =>
      match decode_expr params a,decode_expr params b with
      | Some a,Some b=> match op with
        1=>Some (Recur a b) | 3=>Some (And a b) | 5=>Some (Binary Equal a b)
        | 6=>Some (Binary MakeCons a b) | 9=>Some (Binary Greater a b) | 10=>Some (Binary Subtract a b) | _=>None end
      | _,_=>None end
  | _=>None end
with decode_cond params raw : option expr :=
  match raw with
  | Nil=>Some Fail
  | Cell (Cell test (Cell branch Nil)) rest=>
      match decode_expr params test,decode_expr params branch,decode_cond params rest with
      | Some test,Some branch,Some rest=>Some (If test branch rest) | _,_,_=>None end
  | _=>None end.
Definition decode_definition raw :=
  match raw with
  | Cell (Sym 0) (Cell (Sym 1) (Cell (Cell (Sym x) (Cell (Sym y) Nil)) (Cell body Nil))) =>
      if x =? y then None else decode_expr [x;y] body
  | _=>None end.
