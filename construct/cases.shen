\\ Untrusted goal-directed proof producer: implication, case analysis on an
\\ enumeration-sorted term, contradiction from distinct constructors,
\\ constructor congruence and backchaining through implicational hypotheses.
\\ It emits only existing R02 rule nodes and the R04 data-induct/disjoint
\\ nodes, and adds no rule, axiom or acceptance flag. Every result is
\\ rechecked by the kernel; a failed search leaves [search-failed] inside the
\\ term, which the kernel rejects. See docs/CONSTRUCTION.md ("Case analysis").
(tc -)

\\ ---- proof-term utilities ---------------------------------------------------
\\ Rewriter output uses only hyp/refl/sym/trans/subst/inst. Moving such a
\\ proof under N new hypotheses renumbers its hypothesis references.
(define vor.cases-renumber
  [hyp I] N -> [hyp (+ I N)]
  [sym E] N -> [sym (vor.cases-renumber E N)]
  [trans M A B] N -> [trans M (vor.cases-renumber A N) (vor.cases-renumber B N)]
  [subst S Mo L R Eq B] N ->
    [subst S Mo L R (vor.cases-renumber Eq N) (vor.cases-renumber B N)]
  [inst S B T E] N -> [inst S B T (vor.cases-renumber E N)]
  E _ -> E)
(define vor.cases-failed?
  search-failed -> true
  [X | Xs] -> (or (vor.cases-failed? X) (vor.cases-failed? Xs))
  _ -> false)
(define vor.cases-first
  P Alternative -> (if (vor.cases-failed? P) (thaw Alternative) P))

(define vor.cases-ctor?
  Sig [app C _] -> (not (= (vor.algebra-constructor C Sig) missing))
  _ _ -> false)
(define vor.cases-clash?
  Sig [app C As] [app D Bs] ->
    (and (not (= C D))
      (and (vor.cases-ctor? Sig [app C As]) (vor.cases-ctor? Sig [app D Bs])))
  _ _ _ -> false)
(define vor.cases-enumeration?
  Sig S -> (vor.cases-nullary? (vor.algebra-data S Sig)))
(define vor.cases-nullary?
  [constructors Cs] -> (vor.cases-all-nullary? Cs)
  _ -> false)
(define vor.cases-all-nullary?
  [] -> true
  [[_ []] | Cs] -> (vor.cases-all-nullary? Cs)
  _ -> false)

\\ ---- scripts -------------------------------------------------------------------
\\ Script steps consume the leading quantifiers of the goal: gen introduces a
\\ variable, induct does data-induct on it (each branch continues with the
\\ rest of the script). An exhausted script hands the goal to vor.cases-auto.
(define vor.prove-script
  Sig V G P Script Fuel -> (vor.cases-script Sig V G P Script Fuel 4))
\\ Depth bounds nested backchaining and case splits (2^Depth branches at most).
(define vor.prove-script-depth
  Sig V G P Script Fuel Depth -> (vor.cases-script Sig V G P Script Fuel Depth))
(define vor.cases-script
  Sig V G P [] Fuel D -> (vor.cases-auto Sig V G P Fuel D)
  Sig V G [forall S P] [gen | Rest] Fuel D ->
    [gen (vor.cases-script Sig [S | V] (vor.fol-shift-context G 1) P Rest Fuel D)]
  Sig V G [forall S P] [induct | Rest] Fuel D ->
    [data-induct (vor.cases-branches Sig V G S P Rest Fuel D (vor.algebra-data S Sig))]
  _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-branches
  Sig V G S P Rest Fuel D [constructors Cs] -> (vor.cases-each Sig V G S P Rest Fuel D Cs)
  _ _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-each
  _ _ _ _ _ _ _ _ [] -> []
  Sig V G S P Rest Fuel D [[C Fields] | Cs] ->
    (let N (length Fields)
         Lifted (vor.fol-shift P N 1)
         Gamma (append (vor.algebra-hypotheses S Lifted Fields 0)
                       (vor.fol-shift-context G N))
         Target (vor.fol-sub Lifted [app C (vor.algebra-variables N 0)] 0)
      [[C (vor.cases-script Sig (append Fields V) Gamma Target Rest Fuel D)] |
        (vor.cases-each Sig V G S P Rest Fuel D Cs)]))

\\ ---- automatic search -----------------------------------------------------------
(define vor.cases-auto
  _ _ _ _ _ 0 -> [search-failed]
  _ _ _ [top] _ _ -> [top]
  Sig V G [forall S P] Fuel D ->
    [gen (vor.cases-auto Sig [S | V] (vor.fol-shift-context G 1) P Fuel D)]
  Sig V G [and P Q] Fuel D ->
    [pair (vor.cases-auto Sig V G P Fuel D) (vor.cases-auto Sig V G Q Fuel D)]
  Sig V G [imp P Q] Fuel D -> [intro (vor.cases-assume Sig V G P Q Fuel D)]
  Sig V G [equal S L R] Fuel D -> (vor.cases-equal Sig V G S L R Fuel D)
  _ _ _ _ _ _ -> [search-failed])

\\ Assume P (it becomes hypothesis 0) and prove Q. An equality hypothesis is
\\ normalized in the context *before* it is added, so it cannot rewrite itself.
\\ Distinct constructor normal forms close the goal by disjoint; otherwise the
\\ normalized copy is added, oriented so a constructor side is the result.
(define vor.cases-assume
  Sig V G [equal S L R] Q Fuel D ->
    (vor.cases-assume-normal Sig V G S L R Q Fuel D
      (vor.eq-normal Sig G L Fuel) (vor.eq-normal Sig G R Fuel))
  Sig V G P Q Fuel D -> (vor.cases-auto Sig V [P | G] Q Fuel D))
(define vor.cases-assume-normal
  Sig V G S L R Q Fuel D [normal L1 A] [normal R1 B] ->
    (vor.cases-assume-fact Sig V [[equal S L R] | G] S L1 R1 Q Fuel D
      [trans L [sym (vor.cases-renumber A 1)] [trans R [hyp 0] (vor.cases-renumber B 1)]])
  Sig V G S L R Q Fuel D _ _ -> (vor.cases-auto Sig V [[equal S L R] | G] Q Fuel D))
(define vor.cases-assume-fact
  Sig V [H | G] S L1 R1 Q Fuel D E ->
    (if (vor.cases-clash? Sig L1 R1)
      [exfalso [disjoint L1 R1 E]]
      (if (= L1 R1)
        (vor.cases-auto Sig V [H | G] Q Fuel D)
        (if (and (vor.cases-ctor? Sig L1) (not (vor.cases-ctor? Sig R1)))
          (vor.cases-add-fact Sig V [H | G] [equal S R1 L1] [sym E] Q Fuel D)
          (vor.cases-add-fact Sig V [H | G] [equal S L1 R1] E Q Fuel D)))))
(define vor.cases-add-fact
  Sig V [H | G] H Proof Q Fuel D -> (vor.cases-auto Sig V [H | G] Q Fuel D)
  Sig V G Fact Proof Q Fuel D ->
    [apply Fact [intro (vor.cases-auto Sig V [Fact | G] Q Fuel D)] Proof])

\\ Equality: rewrite both sides; if the normal forms differ, try in order a
\\ contradictory hypothesis, constructor congruence, backchaining and a case
\\ split on an enumeration-sorted subterm.
(define vor.cases-equal
  Sig V G S L R Fuel D ->
    (vor.cases-equal-normal Sig V G S Fuel D
      (vor.eq-normal Sig G L Fuel) (vor.eq-normal Sig G R Fuel)))
(define vor.cases-equal-normal
  Sig V G S Fuel D [normal L1 A] [normal R1 B] ->
    (if (= L1 R1)
      [trans L1 A [sym B]]
      (vor.cases-wrap L1 R1 A B (vor.cases-normal-goal Sig V G S L1 R1 Fuel D)))
  _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-wrap
  L1 R1 A B P -> (if (vor.cases-failed? P) [search-failed] [trans L1 A [trans R1 P [sym B]]]))
(define vor.cases-normal-goal
  Sig V G S L R Fuel D ->
    (vor.cases-first (vor.cases-refute Sig G Fuel)
      (freeze (vor.cases-first (vor.cases-congruence Sig V G S L R Fuel D)
        (freeze (vor.cases-first (vor.cases-backchain Sig V G [equal S L R] Fuel D)
          (freeze (vor.cases-split-goal Sig V G [equal S L R] L R Fuel D))))))))

\\ A ground equality hypothesis whose two sides normalize to distinct
\\ constructors refutes the context. It is normalized with itself masked.
(define vor.cases-refute
  Sig G Fuel -> (vor.cases-refute-at Sig G G 0 Fuel))
(define vor.cases-refute-at
  _ _ [] _ _ -> [search-failed]
  Sig G [[equal S L R] | Hs] I Fuel ->
    (let Masked (vor.replace-at G I [top])
      (vor.cases-refute-try Sig G Hs I Fuel L R
        (vor.eq-normal Sig Masked L Fuel) (vor.eq-normal Sig Masked R Fuel)))
  Sig G [_ | Hs] I Fuel -> (vor.cases-refute-at Sig G Hs (+ I 1) Fuel))
(define vor.cases-refute-try
  Sig G Hs I Fuel L R [normal L1 A] [normal R1 B] ->
    (if (vor.cases-clash? Sig L1 R1)
      [exfalso [disjoint L1 R1 [trans L [sym A] [trans R [hyp I] B]]]]
      (vor.cases-refute-at Sig G Hs (+ I 1) Fuel))
  Sig G Hs I Fuel _ _ _ _ -> (vor.cases-refute-at Sig G Hs (+ I 1) Fuel))

\\ Same constructor on both sides: prove the fields equal, then rebuild the
\\ application by repeated substitution (the rewriter's congruence chain).
(define vor.cases-congruence
  Sig V G S [app C As] [app C Bs] Fuel D ->
    (vor.cases-congruence-fields Sig V G C As Bs Fuel D (vor.algebra-constructor C Sig))
  _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-congruence-fields
  Sig V G C As Bs Fuel D [function Fields Result] ->
    (let Es (vor.cases-field-proofs Sig V G As Bs Fields Fuel D)
      (if (vor.cases-failed? Es)
        [search-failed]
        (vor.eq-cong-steps C As Bs Es Fields Result 0 [refl])))
  _ _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-field-proofs
  _ _ _ [] [] [] _ _ -> []
  Sig V G [A | As] [B | Bs] [F | Fs] Fuel D ->
    [(if (= A B) [refl] (vor.cases-equal Sig V G F A B Fuel D)) |
      (vor.cases-field-proofs Sig V G As Bs Fs Fuel D)]
  _ _ _ _ _ _ _ _ -> [search-failed])

\\ Backchaining: a hypothesis forall Xs. Pre -> L = R whose conclusion
\\ matches the goal is instantiated, and Pre is proved recursively.
(define vor.cases-backchain
  Sig V G Goal Fuel D -> (vor.cases-backchain-at Sig V G G 0 Goal Fuel D))
(define vor.cases-backchain-at
  _ _ _ [] _ _ _ _ -> [search-failed]
  Sig V G [H | Hs] I Goal Fuel D ->
    (vor.cases-first (vor.cases-backchain-one Sig V G H I Goal Fuel D)
      (freeze (vor.cases-backchain-at Sig V G Hs (+ I 1) Goal Fuel D))))
(define vor.cases-backchain-one
  Sig V G H I Goal Fuel D ->
    (vor.cases-backchain-rule Sig V G H I Goal Fuel D (vor.cases-imp-strip H [])))
(define vor.cases-imp-strip
  [forall S P] Ss -> (vor.cases-imp-strip P [S | Ss])
  [imp Pre [equal S L R]] Ss -> [rule Ss Pre S L R]
  _ _ -> missing)
(define vor.cases-backchain-rule
  Sig V G H I [equal S A B] Fuel D [rule Ss Pre S L R] ->
    (vor.cases-backchain-match Sig V G H I [equal S A B] Fuel D (length Ss)
      (vor.eq-match-next [R] [B] (length Ss) (vor.eq-match L A (length Ss) [])))
  _ _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-backchain-match
  Sig V G H I Goal Fuel D N [matches Bs] ->
    (if (= N (length Bs))
      (vor.cases-backchain-bound Sig V G H I Goal Fuel D (vor.eq-bound-terms Bs))
      [search-failed])
  _ _ _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-backchain-bound
  Sig V G H I Goal Fuel D [terms Ts] ->
    (vor.cases-backchain-inst Sig V G Goal Fuel D
      (vor.eq-instantiate H (reverse Ts)) (vor.proof-specialize H (reverse Ts) [hyp I]))
  _ _ _ _ _ _ _ _ _ -> [search-failed])
(define vor.cases-backchain-inst
  Sig V G Goal Fuel D [imp Pre Goal] Spec ->
    (let P (vor.cases-auto Sig V G Pre Fuel (- D 1))
      (if (vor.cases-failed? P) [search-failed] [apply Pre Spec P]))
  _ _ _ _ _ _ _ _ -> [search-failed])

\\ Case split on the innermost non-constructor subterm of an enumeration
\\ sort: prove forall Z. T = Z -> Goal by data-induct, instantiate Z := T and
\\ discharge T = T by refl. Each branch assumes T = C, which then rewrites T.
\\ Candidates come from the goal, then from ground equality hypotheses; a term
\\ already equated to a constructor by a hypothesis is decided and skipped.
(define vor.cases-split-goal
  Sig V G Goal L R Fuel D ->
    (let Ds (vor.cases-decided Sig G)
      (vor.cases-split Sig V G Goal Fuel D
        (vor.cases-candidate-terms Sig V Ds (append [L R] (vor.cases-hypothesis-sides G))))))
(define vor.cases-decided
  _ [] -> []
  Sig [[equal _ T C] | Hs] ->
    (if (and (vor.cases-ctor? Sig C) (not (vor.cases-ctor? Sig T)))
      [T | (vor.cases-decided Sig Hs)] (vor.cases-decided Sig Hs))
  Sig [_ | Hs] -> (vor.cases-decided Sig Hs))
(define vor.cases-hypothesis-sides
  [] -> []
  [[equal _ L R] | Hs] -> [L R | (vor.cases-hypothesis-sides Hs)]
  [_ | Hs] -> (vor.cases-hypothesis-sides Hs))
(define vor.cases-candidate-or
  missing Alternative -> (thaw Alternative)
  Found _ -> Found)
(define vor.cases-candidate-terms
  _ _ _ [] -> missing
  Sig V Ds [T | Ts] ->
    (vor.cases-candidate-or (vor.cases-candidate Sig V Ds T)
      (freeze (vor.cases-candidate-terms Sig V Ds Ts))))
(define vor.cases-candidate
  Sig V Ds [app F Ts] ->
    (vor.cases-candidate-or (vor.cases-candidate-terms Sig V Ds Ts)
      (freeze (vor.cases-candidate-self Sig V Ds [app F Ts])))
  _ _ _ _ -> missing)
(define vor.cases-candidate-self
  Sig V Ds T ->
    (if (or (vor.cases-ctor? Sig T) (vor.member? T Ds)) missing
      (vor.cases-candidate-sort T (vor.fol-term-sort Sig V T) Sig)))
(define vor.cases-candidate-sort
  T [sort S] Sig -> (if (vor.cases-enumeration? Sig S) [split T S] missing)
  _ _ _ -> missing)
(define vor.cases-split
  _ _ _ _ _ 1 _ -> [search-failed]
  Sig V G Goal Fuel D [split T S] ->
    (let Body [imp [equal S (vor.fol-shift-term T 1 0) [v 0]] (vor.fol-shift Goal 1 0)]
         Branches (vor.cases-branches Sig V G S Body [] Fuel (- D 1) (vor.algebra-data S Sig))
      (if (vor.cases-failed? Branches)
        [search-failed]
        [apply [equal S T T] [inst S Body T [data-induct Branches]] [refl]]))
  _ _ _ _ _ _ _ -> [search-failed])

\\ ---- lemma chains -----------------------------------------------------------------
\\ [[Formula Script] ...] oldest first. Each lemma is proved in the context of
\\ the equations and the lemmas before it, then introduced as a hypothesis by
\\ [apply L [intro Rest] LProof]. Nothing is assumed.
(define vor.prove-with-lemmas
  Sig G [] Target Script Fuel -> (vor.prove-script Sig [] G Target Script Fuel)
  Sig G [[L LScript] | Ls] Target Script Fuel ->
    [apply L
      [intro (vor.prove-with-lemmas Sig [L | G] Ls Target Script Fuel)]
      (vor.prove-script Sig [] G L LScript Fuel)])
