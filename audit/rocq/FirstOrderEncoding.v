From Coq Require Import List Arith Bool.
From VorAudit Require Import NativeLookup FirstOrderSyntax FirstOrderSemantics FirstOrderKernel.
Import ListNotations.
Set Implicit Arguments.
Module FS := FirstOrderSyntax.
Module FK := FirstOrderKernel.
Module NV := NativeLookup.
Definition raw_list xs := fold_right NV.Cell NV.Nil xs.
Definition tagged tag xs := NV.Cell (NV.Sym tag) (raw_list xs).
Fixpoint encode_term t := match t with
  | FS.Var n => tagged 4 [NV.Num n]
  | FS.App f ts => tagged 5 [NV.Sym f;encode_terms ts] end
with encode_terms ts := match ts with
  | FS.TNil=>NV.Nil | FS.TCons t rest=>NV.Cell (encode_term t) (encode_terms rest) end.
Fixpoint decode_term raw : option FS.term := match raw with
  | NV.Cell (NV.Sym 4) (NV.Cell (NV.Num n) NV.Nil)=>Some (FS.Var n)
  | NV.Cell (NV.Sym 5) (NV.Cell (NV.Sym f) (NV.Cell ts NV.Nil))=>
      option_map (FS.App f) (decode_terms ts)
  | _=>None end
with decode_terms raw : option FS.terms := match raw with
  | NV.Nil=>Some FS.TNil
  | NV.Cell t rest=>match decode_term t,decode_terms rest with
      Some t,Some rest=>Some (FS.TCons t rest) | _,_=>None end
  | _=>None end.
Fixpoint encode_formula p := match p with
  | FS.Top=>tagged 6 [] | FS.Bottom=>tagged 7 []
  | FS.Pred f ts=>tagged 8 [NV.Sym f;encode_terms ts]
  | FS.Equal s a b=>tagged 9 [NV.Sym s;encode_term a;encode_term b]
  | FS.And p q=>tagged 10 [encode_formula p;encode_formula q]
  | FS.Or p q=>tagged 11 [encode_formula p;encode_formula q]
  | FS.Imp p q=>tagged 12 [encode_formula p;encode_formula q]
  | FS.All s p=>tagged 13 [NV.Sym s;encode_formula p]
  | FS.Ex s p=>tagged 14 [NV.Sym s;encode_formula p] end.
Definition combine2 {A B C} (f:A->B->C) a b :=
  match a,b with Some a,Some b=>Some (f a b) | _,_=>None end.
Fixpoint decode_formula raw : option FS.formula := match raw with
  | NV.Cell (NV.Sym 6) NV.Nil=>Some FS.Top
  | NV.Cell (NV.Sym 7) NV.Nil=>Some FS.Bottom
  | NV.Cell (NV.Sym 8) (NV.Cell (NV.Sym f) (NV.Cell ts NV.Nil))=>option_map (FS.Pred f) (decode_terms ts)
  | NV.Cell (NV.Sym 9) (NV.Cell (NV.Sym s) (NV.Cell a (NV.Cell b NV.Nil)))=>
      combine2 (FS.Equal s) (decode_term a) (decode_term b)
  | NV.Cell (NV.Sym op) (NV.Cell a (NV.Cell b NV.Nil))=>
      match op with
      10=>combine2 FS.And (decode_formula a) (decode_formula b)
      |11=>combine2 FS.Or (decode_formula a) (decode_formula b)
      |12=>combine2 FS.Imp (decode_formula a) (decode_formula b)
      |13=>match a with NV.Sym s=>option_map (FS.All s) (decode_formula b) | _=>None end
      |14=>match a with NV.Sym s=>option_map (FS.Ex s) (decode_formula b) | _=>None end
      |_=>None end
  |_=>None end.
Theorem term_roundtrip :
  (forall t, decode_term (encode_term t)=Some t) /\
  (forall ts, decode_terms (encode_terms ts)=Some ts).
Proof. apply FS.term_induction; intros; simpl; unfold tagged in *; simpl; rewrite ?H, ?H0; reflexivity. Qed.
Theorem formula_roundtrip : forall p, decode_formula (encode_formula p)=Some p.
Proof.
  induction p; simpl; unfold tagged in *; simpl;
    rewrite ?(proj1 term_roundtrip), ?(proj2 term_roundtrip), ?IHp, ?IHp1, ?IHp2; reflexivity.
Qed.
Theorem term_encoding_injective : forall a b, encode_term a=encode_term b -> a=b.
Proof. intros a b E; apply (f_equal decode_term) in E; rewrite !(proj1 term_roundtrip) in E; congruence. Qed.
Theorem formula_encoding_injective : forall a b, encode_formula a=encode_formula b -> a=b.
Proof. intros a b E; apply (f_equal decode_formula) in E; rewrite !formula_roundtrip in E; congruence. Qed.

Fixpoint decode_symbols raw : option (list nat) := match raw with
  | NV.Nil=>Some []
  | NV.Cell (NV.Sym n) rest=>option_map (cons n) (decode_symbols rest)
  |_=>None end.
Fixpoint decode_formulas raw : option (list FS.formula) := match raw with
  | NV.Nil=>Some []
  | NV.Cell p rest=>combine2 (@cons FS.formula) (decode_formula p) (decode_formulas rest)
  |_=>None end.
Fixpoint decode_proof raw : option FK.proof := match raw with
  | NV.Cell (NV.Sym 15) (NV.Cell (NV.Num n) NV.Nil)=>Some (FK.Hyp n)
  | NV.Cell (NV.Sym 6) NV.Nil=>Some FK.Unit
  | NV.Cell (NV.Sym 16) (NV.Cell a (NV.Cell b NV.Nil))=>combine2 FK.Pair (decode_proof a) (decode_proof b)
  | NV.Cell (NV.Sym 17) (NV.Cell q (NV.Cell e NV.Nil))=>combine2 FK.Fst (decode_formula q) (decode_proof e)
  | NV.Cell (NV.Sym 18) (NV.Cell p (NV.Cell e NV.Nil))=>combine2 FK.Snd (decode_formula p) (decode_proof e)
  | NV.Cell (NV.Sym 19) (NV.Cell e NV.Nil)=>option_map FK.Intro (decode_proof e)
  | NV.Cell (NV.Sym 20) (NV.Cell p (NV.Cell a (NV.Cell b NV.Nil)))=>
      match decode_formula p,decode_proof a,decode_proof b with Some p,Some a,Some b=>Some (FK.Apply p a b) |_,_,_=>None end
  | NV.Cell (NV.Sym 21) (NV.Cell e NV.Nil)=>option_map FK.Inl (decode_proof e)
  | NV.Cell (NV.Sym 22) (NV.Cell e NV.Nil)=>option_map FK.Inr (decode_proof e)
  | NV.Cell (NV.Sym 23) (NV.Cell p (NV.Cell q (NV.Cell e (NV.Cell a (NV.Cell b NV.Nil)))))=>
      match decode_formula p,decode_formula q,decode_proof e,decode_proof a,decode_proof b with
        Some p,Some q,Some e,Some a,Some b=>Some (FK.Cases p q e a b) |_,_,_,_,_=>None end
  | NV.Cell (NV.Sym 24) (NV.Cell e NV.Nil)=>option_map FK.Exfalso (decode_proof e)
  | NV.Cell (NV.Sym 25) (NV.Cell e NV.Nil)=>option_map FK.Gen (decode_proof e)
  | NV.Cell (NV.Sym 26) (NV.Cell (NV.Sym s) (NV.Cell p (NV.Cell t (NV.Cell e NV.Nil))))=>
      match decode_formula p,decode_term t,decode_proof e with Some p,Some t,Some e=>Some (FK.Inst s p t e) |_,_,_=>None end
  | NV.Cell (NV.Sym 27) (NV.Cell t (NV.Cell e NV.Nil))=>combine2 FK.Witness (decode_term t) (decode_proof e)
  | NV.Cell (NV.Sym 28) (NV.Cell (NV.Sym s) (NV.Cell p (NV.Cell e (NV.Cell b NV.Nil))))=>
      match decode_formula p,decode_proof e,decode_proof b with Some p,Some e,Some b=>Some (FK.Unpack s p e b) |_,_,_=>None end
  | NV.Cell (NV.Sym 29) NV.Nil=>Some FK.Refl
  | NV.Cell (NV.Sym 30) (NV.Cell e NV.Nil)=>option_map FK.Sym (decode_proof e)
  | NV.Cell (NV.Sym 31) (NV.Cell t (NV.Cell a (NV.Cell b NV.Nil)))=>
      match decode_term t,decode_proof a,decode_proof b with Some t,Some a,Some b=>Some (FK.Trans t a b) |_,_,_=>None end
  | NV.Cell (NV.Sym 32) (NV.Cell (NV.Sym s) (NV.Cell p (NV.Cell l (NV.Cell r (NV.Cell a (NV.Cell b NV.Nil))))))=>
      match decode_formula p,decode_term l,decode_term r,decode_proof a,decode_proof b with
        Some p,Some l,Some r,Some a,Some b=>Some (FK.Subst s p l r a b) |_,_,_,_,_=>None end
  | NV.Cell (NV.Sym 33) (NV.Cell a (NV.Cell b NV.Nil))=>combine2 FK.TreeInduct (decode_proof a) (decode_proof b)
  |_=>None end.

Fixpoint decode_functions raw : option (list (nat*(list nat*nat))) := match raw with
  | NV.Nil=>Some []
  | NV.Cell (NV.Cell (NV.Sym f) (NV.Cell ss (NV.Cell (NV.Sym s) NV.Nil))) rest=>
      combine2 (fun ss rest=>(f,(ss,s))::rest) (decode_symbols ss) (decode_functions rest)
  |_=>None end.
Fixpoint decode_predicates raw : option (list (nat*list nat)) := match raw with
  | NV.Nil=>Some []
  | NV.Cell (NV.Cell (NV.Sym p) (NV.Cell ss NV.Nil)) rest=>
      combine2 (fun ss rest=>(p,ss)::rest) (decode_symbols ss) (decode_predicates rest)
  |_=>None end.
Fixpoint lookup {A} n (xs:list (nat*A)) := match xs with
  | []=>None | (k,v)::rest=>if n=?k then Some v else lookup n rest end.
Definition signature_of sorts fs ps :=
  FirstOrderSemantics.Sig
    (fun f=>if f=?1 then Some ([],0) else if f=?2 then Some ([0;0],0) else lookup f fs)
    (fun p=>lookup p ps) (fun s=>existsb (Nat.eqb s) (0::sorts)).
Fixpoint distinct ns := match ns with []=>true | n::ns=>negb (existsb (Nat.eqb n) ns) && distinct ns end.
Definition signature_valid sorts fs ps :=
  let known s := existsb (Nat.eqb s) (0::sorts) in
  distinct sorts && negb (existsb (Nat.eqb 0) sorts) &&
  distinct (map fst fs) && distinct (map fst ps) &&
  forallb (fun entry=>let '(f,(args,result)):=entry in
    negb (f=?1) && negb (f=?2) && forallb known args && known result && negb (result=?0)) fs &&
  forallb (fun entry=>forallb known (snd entry)) ps.
Definition decode_signature raw : option FirstOrderSemantics.signature := match raw with
  | NV.Cell (NV.Sym 3) (NV.Cell (NV.Num 0) (NV.Cell ss (NV.Cell fs (NV.Cell ps NV.Nil))))=>
      match decode_symbols ss,decode_functions fs,decode_predicates ps with
        Some ss,Some fs,Some ps=>if signature_valid ss fs ps then Some (signature_of ss fs ps) else None |_,_,_=>None end
  |_=>None end.
Definition decode_goal v g p e : option FK.goal :=
  match decode_symbols v,decode_formulas g,decode_formula p,decode_proof e with
    Some v,Some g,Some p,Some e=>Some (FK.G v g p e) |_,_,_,_=>None end.
Definition raw_check rawsig v g p e fuel :=
  match decode_signature rawsig,decode_goal v g p e with
  | Some sig,Some goal=> match Checker.check (FK.expand sig) fuel [goal] with Some _=>true |None=>false end
  |_,_=>false end.

(* This theorem connects the executable raw-data boundary to the universal
   semantic result. It never trusts an external parser's claimed formula. *)
Theorem raw_acceptance_decodes : forall rawsig v g p e fuel,
  raw_check rawsig v g p e fuel = true -> exists sig goal rem,
    decode_signature rawsig=Some sig /\ decode_goal v g p e=Some goal /\
    Checker.check (FK.expand sig) fuel [goal]=Some rem.
Proof.
  intros. unfold raw_check in H. destruct (decode_signature rawsig) as [sig|] eqn:S; try discriminate.
  destruct (decode_goal v g p e) as [goal|] eqn:G; try discriminate.
  destruct (Checker.check (FK.expand sig) fuel [goal]) eqn:C; try discriminate. eauto 10.
Qed.

Theorem raw_checker_sound : forall rawsig v g p e fuel sig goal,
  decode_signature rawsig=Some sig -> decode_goal v g p e=Some goal ->
  raw_check rawsig v g p e fuel=true ->
  forall (D:Type) (fn:nat->list D->D) (pred:nat->list D->Prop) (belongs:nat->D->Prop),
  (forall f ss s values, FirstOrderSemantics.function_signature sig f=Some (ss,s) ->
    Forall2 belongs ss values -> belongs s (fn f values)) ->
  forall encode_tree:FK.tree->D,
  (forall value, belongs 0 value <-> exists t,encode_tree t=value) ->
  fn 1 []=encode_tree FK.Leaf ->
  (forall l r,fn 2 [encode_tree l;encode_tree r]=encode_tree (FK.Node l r)) ->
  FK.valid fn pred belongs goal.
Proof.
  intros rawsig v g p e fuel sig goal S G A D fn pred belongs FT enc TV TL TN.
  apply raw_acceptance_decodes in A as [s [t [rem [DS [DG CHECK]]]]].
  rewrite S in DS; inversion DS; subst s. rewrite G in DG; inversion DG; subst t.
  exact (@FK.checker_sound D fn pred belongs sig FT enc TV TL TN fuel goal rem CHECK).
Qed.
