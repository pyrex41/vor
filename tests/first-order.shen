(tc -)
(define fol-test.signature
  -> [fol-signature 0 [person other]
       [[a [] person] [b [] person] [f [person] person] [z [] other]]
       [[p [person]] [q [person]] [r [person person]] [tree-p [vor.tree]] [flag []]]])
(define fol-test.a -> [app a []])
(define fol-test.b -> [app b []])
(define fol-test.p -> [pred p [(fol-test.a)]])
(define fol-test.q -> [pred q [(fol-test.a)]])
(set *fol-test-cases* [])
(define fol-test.case
  Name V G P E Status ->
    (do (test.equal Name (hd (vor.fol-check (fol-test.signature) V G P E 1000)) Status)
      (do (test.equal Name (hd (vor.fol-typecheck (fol-test.signature) V G P E)) Status)
        (do (set *fol-test-cases* [[case Name V G P E Status] | (value *fol-test-cases*)]) checked))))

(test.equal fol-signature (vor.fol-signature? (fol-test.signature)) true)
(test.equal empty-signature (vor.fol-signature? [fol-signature 0 [] [] []]) true)
(test.equal duplicate-sort (vor.fol-signature? [fol-signature 0 [s s] [] []]) false)
(test.equal unknown-arg-sort (vor.fol-signature? [fol-signature 0 [] [[f [bad] bad]] []]) false)
(test.equal duplicate-function (vor.fol-signature? [fol-signature 0 [s] [[a [] s] [a [] s]] []]) false)
(test.equal duplicate-predicate (vor.fol-signature? [fol-signature 0 [] [] [[p []] [p []]]]) false)
(test.equal reserved-sort (vor.fol-signature? [fol-signature 0 [vor.tree] [] []]) false)
(test.equal reserved-constructor (vor.fol-signature? [fol-signature 0 [s] [[vor.node [] s]] []]) false)
(test.equal no-new-tree-constructor (vor.fol-signature? [fol-signature 0 [] [[extra [] vor.tree]] []]) false)
(test.equal malformed-signature (vor.fol-signature? [fol-signature 0 [s] [bad] []]) false)
(test.equal open-variable (vor.fol-term-sort (fol-test.signature) [person] [v 0]) [sort person])
(test.equal dangling-variable (vor.fol-term-sort (fol-test.signature) [] [v 0]) invalid)
(test.equal negative-variable (vor.fol-term-sort (fol-test.signature) [person] [v -1]) invalid)
(test.equal fractional-variable (vor.fol-term-sort (fol-test.signature) [person] [v 0.5]) invalid)
(test.equal function-arity (vor.fol-term-sort (fol-test.signature) [] [app f []]) invalid)
(test.equal function-sort (vor.fol-term-sort (fol-test.signature) [] [app f [[app z []]]]) invalid)
(test.equal unknown-function (vor.fol-term-sort (fol-test.signature) [] [app eval []]) invalid)
(test.equal no-executable-term (vor.fol-term-sort (fol-test.signature) [] [simple-error "no"]) invalid)
(test.equal unknown-predicate (vor.fol-formula? (fol-test.signature) [] [pred unknown []]) false)
(test.equal bad-predicate-sort (vor.fol-formula? (fol-test.signature) [] [pred p [[app z []]]]) false)
(test.equal wrong-equality-sort (vor.fol-formula? (fol-test.signature) [] [equal other (fol-test.a) (fol-test.a)]) false)
(test.equal malformed-sequent
  (vor.fol-check (fol-test.signature) [] [] [pred p [[v 0]]] [hyp 0] 20)
  [rejected malformed-first-order-sequent])

(fol-test.case hyp [] [(fol-test.p)] (fol-test.p) [hyp 0] accepted)
(fol-test.case hyp-index [] [(fol-test.q) (fol-test.p)] (fol-test.p) [hyp 1] accepted)
(fol-test.case hyp-wrong [] [(fol-test.q)] (fol-test.p) [hyp 0] rejected)
(fol-test.case hyp-negative [] [(fol-test.p)] (fol-test.p) [hyp -1] rejected)
(fol-test.case top [] [] [top] [top] accepted)
(fol-test.case top-wrong [] [] [bottom] [top] rejected)
(fol-test.case pair [] [(fol-test.p) (fol-test.q)] [and (fol-test.p) (fol-test.q)] [pair [hyp 0] [hyp 1]] accepted)
(fol-test.case pair-wrong [] [(fol-test.p)] [and (fol-test.p) (fol-test.q)] [pair [hyp 0] [hyp 0]] rejected)
(fol-test.case fst [] [[and (fol-test.p) (fol-test.q)]] (fol-test.p) [fst (fol-test.q) [hyp 0]] accepted)
(fol-test.case fst-wrong [] [(fol-test.p)] (fol-test.p) [fst (fol-test.q) [hyp 0]] rejected)
(fol-test.case snd [] [[and (fol-test.p) (fol-test.q)]] (fol-test.q) [snd (fol-test.p) [hyp 0]] accepted)
(fol-test.case snd-wrong [] [[and (fol-test.p) (fol-test.q)]] (fol-test.p) [snd (fol-test.p) [hyp 0]] rejected)
(fol-test.case imp-intro [] [] [imp (fol-test.p) (fol-test.p)] [intro [hyp 0]] accepted)
(fol-test.case assumption-leak [] [] [and [imp (fol-test.p) (fol-test.p)] (fol-test.p)] [pair [intro [hyp 0]] [hyp 0]] rejected)
(fol-test.case imp-elim [] [[imp (fol-test.p) (fol-test.q)] (fol-test.p)] (fol-test.q)
  [apply (fol-test.p) [hyp 0] [hyp 1]] accepted)
(fol-test.case imp-elim-wrong [] [[imp (fol-test.p) (fol-test.q)]] (fol-test.q)
  [apply (fol-test.p) [hyp 0] [top]] rejected)
(fol-test.case or-left [] [(fol-test.p)] [or (fol-test.p) (fol-test.q)] [inl [hyp 0]] accepted)
(fol-test.case or-left-wrong [] [(fol-test.q)] [or (fol-test.p) (fol-test.q)] [inl [hyp 0]] rejected)
(fol-test.case or-right [] [(fol-test.q)] [or (fol-test.p) (fol-test.q)] [inr [hyp 0]] accepted)
(fol-test.case or-right-wrong [] [(fol-test.p)] [or (fol-test.p) (fol-test.q)] [inr [hyp 0]] rejected)
(fol-test.case or-elim [] [[or (fol-test.p) (fol-test.q)]] [or (fol-test.q) (fol-test.p)]
  [cases (fol-test.p) (fol-test.q) [hyp 0] [inr [hyp 0]] [inl [hyp 0]]] accepted)
(fol-test.case or-missing-branch [] [[or (fol-test.p) (fol-test.q)]] (fol-test.p)
  [cases (fol-test.p) (fol-test.q) [hyp 0] [hyp 0] [hyp 0]] rejected)
(fol-test.case bottom-elim [] [[bottom]] (fol-test.p) [exfalso [hyp 0]] accepted)
(fol-test.case forged-bottom [] [] (fol-test.p) [exfalso [top]] rejected)
(fol-test.case all-intro [] [] [forall person [equal person [v 0] [v 0]]] [gen [refl]] accepted)
(fol-test.case bad-generalization [person] [[pred p [[v 0]]]] [forall person [pred p [[v 0]]]] [gen [hyp 0]] rejected)
(fol-test.case valid-weakening [person] [[pred p [[v 0]]]] [forall other [pred p [[v 1]]]] [gen [hyp 0]] accepted)
(fol-test.case all-elim [] [[forall person [pred p [[v 0]]]]] (fol-test.p)
  [inst person [pred p [[v 0]]] (fol-test.a) [hyp 0]] accepted)
(fol-test.case inst-wrong-sort [] [[forall person [pred p [[v 0]]]]] (fol-test.p)
  [inst person [pred p [[v 0]]] [app z []] [hyp 0]] rejected)
(fol-test.case exists-intro [] [(fol-test.p)] [exists person [pred p [[v 0]]]]
  [witness (fol-test.a) [hyp 0]] accepted)
(fol-test.case exists-wrong-sort [] [] [exists person [top]] [witness [app z []] [top]] rejected)
(fol-test.case exists-elim [] [[exists person [pred p [[v 0]]]]] [exists person [pred p [[v 0]]]]
  [unpack person [pred p [[v 0]]] [hyp 0] [witness [v 0] [hyp 0]]] accepted)
(fol-test.case witness-escape [person] [[exists person [pred p [[v 0]]]]] [pred p [[v 0]]]
  [unpack person [pred p [[v 0]]] [hyp 0] [hyp 0]] rejected)
(fol-test.case equality-refl [] [] [equal person (fol-test.a) (fol-test.a)] [refl] accepted)
(fol-test.case equality-forged [] [] [equal person (fol-test.a) (fol-test.b)] [refl] rejected)
(fol-test.case equality-sym [] [[equal person (fol-test.a) (fol-test.b)]]
  [equal person (fol-test.b) (fol-test.a)] [sym [hyp 0]] accepted)
(fol-test.case equality-sym-forged [] [] [equal person (fol-test.b) (fol-test.a)] [sym [refl]] rejected)
(fol-test.case equality-trans [] [[equal person (fol-test.a) (fol-test.b)]]
  [equal person (fol-test.a) (fol-test.b)] [trans (fol-test.b) [hyp 0] [refl]] accepted)
(fol-test.case equality-trans-forged [] [] [equal person (fol-test.a) (fol-test.b)]
  [trans (fol-test.a) [refl] [refl]] rejected)
(fol-test.case equality-substitution [] [[equal person (fol-test.a) (fol-test.b)] (fol-test.p)]
  [pred p [(fol-test.b)]] [subst person [pred p [[v 0]]] (fol-test.a) (fol-test.b) [hyp 0] [hyp 1]] accepted)
(fol-test.case equality-substitution-forged [] [(fol-test.p)]
  [pred p [(fol-test.b)]] [subst person [pred p [[v 0]]] (fol-test.a) (fol-test.b) [refl] [hyp 0]] rejected)
(fol-test.case no-admit [] [] [bottom] [admit] rejected)
(fol-test.case no-circular-reference [] [] [bottom] [reference self] rejected)
(fol-test.case no-host-proof [] [] [top] [simple-error "never execute"] rejected)

\\ Explicit named expected vectors, independent of the substitution implementation.
(test.equal substitution-capture
  (vor.fol-instantiate (fol-test.signature) [person] person
    [forall person [pred r [[v 1] [v 0]]]] [v 0])
  [ok [forall person [pred r [[v 1] [v 0]]]]])
(test.equal substitution-index-decrement
  (vor.fol-instantiate (fol-test.signature) [person] person [pred r [[v 0] [v 1]]] (fol-test.a))
  [ok [pred r [(fol-test.a) [v 0]]]])
(test.equal substitution-nested
  (vor.fol-instantiate (fol-test.signature) [person] person
    [forall person [exists person [pred r [[v 2] [v 3]]]]] [v 0])
  [ok [forall person [exists person [pred r [[v 2] [v 2]]]]]])
(test.equal substitution-sort-error
  (vor.fol-instantiate (fol-test.signature) [] person [pred p [[v 0]]] [app z []])
  [rejected malformed-instantiation])
(test.equal no-fuel (vor.fol-check (fol-test.signature) [] [] [top] [top] 0) [unknown proof-fuel])
(test.equal exact-fuel (vor.fol-check (fol-test.signature) [] [] [and [top] [top]] [pair [top] [top]] 3)
  [accepted first-order-derivation])
(test.equal fuel-shared-between-branches
  (vor.fol-check (fol-test.signature) [] [] [and [top] [top]] [pair [top] [top]] 2) [unknown proof-fuel])
(test.equal invalid-fuel (vor.fol-check (fol-test.signature) [] [] [top] [top] -1) [rejected invalid-proof-fuel])
(test.equal no-arbitrary-fuel (vor.fol-check (fol-test.signature) [] [] [top] [top] 65536) [rejected invalid-proof-fuel])

\\ Fixed tree induction: both base and closure hypotheses are genuinely used.
(define fol-test.tree-body -> [pred tree-p [[v 0]]])
(define fol-test.tree-closure-body
  -> [forall vor.tree [imp [pred tree-p [[v 1]]]
       [imp [pred tree-p [[v 0]]] [pred tree-p [[app vor.node [[v 1] [v 0]]]]]]]])
(define fol-test.tree-context
  -> [[pred tree-p [[app vor.leaf []]]] [forall vor.tree (fol-test.tree-closure-body)]])
(define fol-test.tree-step
  -> [apply [pred tree-p [[v 0]]]
       [apply [pred tree-p [[v 1]]]
         [inst vor.tree
           [imp [pred tree-p [[v 2]]]
             [imp [pred tree-p [[v 0]]] [pred tree-p [[app vor.node [[v 2] [v 0]]]]]]]
           [v 0] [inst vor.tree (fol-test.tree-closure-body) [v 1] [hyp 3]]]
         [hyp 0]]
       [hyp 1]])
(fol-test.case tree-induction [] (fol-test.tree-context) [forall vor.tree (fol-test.tree-body)]
  [tree-induct [hyp 0] (fol-test.tree-step)] accepted)
(fol-test.case tree-no-base [] [] [forall vor.tree (fol-test.tree-body)]
  [tree-induct [top] (fol-test.tree-step)] rejected)
(fol-test.case tree-wrong-step [] (fol-test.tree-context) [forall vor.tree (fol-test.tree-body)]
  [tree-induct [hyp 0] [hyp 0]] rejected)
(fol-test.case no-arbitrary-sort-induction [] [] [forall person [pred p [[v 0]]]]
  [tree-induct [top] [top]] rejected)
(fol-test.case tree-frame-preservation [person] [[pred p [[v 0]]]]
  [forall vor.tree [pred p [[v 1]]]] [tree-induct [hyp 0] [hyp 2]] accepted)
(fol-test.case tree-no-eigenvar-leak [vor.tree] []
  [forall vor.tree [equal vor.tree [v 0] [v 1]]] [tree-induct [refl] [refl]] rejected)
(fol-test.case equality-under-binder [person]
  [[equal person (fol-test.a) [v 0]] [forall person [pred r [(fol-test.a) [v 0]]]]]
  [forall person [pred r [[v 1] [v 0]]]]
  [subst person [forall person [pred r [[v 1] [v 0]]]] (fol-test.a) [v 0] [hyp 0] [hyp 1]] accepted)
(fol-test.case equality-capture-attack [person]
  [[equal person (fol-test.a) [v 0]] [forall person [pred r [(fol-test.a) [v 0]]]]]
  [forall person [pred r [[v 0] [v 0]]]]
  [subst person [forall person [pred r [[v 1] [v 0]]]] (fol-test.a) [v 0] [hyp 0] [hyp 1]] rejected)

(test.equal fol-inventory-rules (length (hd (tl (tl (vor.fol-root-inventory))))) 20)
(define fol-test.claim
  -> [vor-claim 0 (test.root) [first-order (fol-test.signature) []] []
       [[runtime trusted-image]] constructive-first-order
       [derives [] [forall person [equal person [v 0] [v 0]]]] concrete-derivation])
(define fol-test.envelope -> [vor-evidence 0 (fol-test.claim) [gen [refl]]])
(test.equal fol-claim-valid (vor.claim? (fol-test.claim)) true)
(test.equal fol-bound-claim
  (vor.check-claim (test.root) (fol-test.claim) (fol-test.envelope) 2)
  [checked (fol-test.claim) [accepted first-order-derivation]])
(test.equal fol-bound-typed
  (vor.typecheck-claim (test.root) (fol-test.claim) (fol-test.envelope))
  [checked (fol-test.claim) [accepted typed-evidence]])
(test.equal fol-bound-wire
  (vor.check-artifact (test.root) (fol-test.claim) (test.ok (test.pack (fol-test.envelope))) 10000 64 10000 2)
  [checked (fol-test.claim) [accepted first-order-derivation]])
(test.equal fol-no-fuel-over-wire
  (vor.check-artifact (test.root) (fol-test.claim) (test.ok (test.pack (fol-test.envelope))) 10000 64 10000 1)
  [unknown proof-fuel])
(test.equal fol-context-substitution
  (vor.check-claim (test.root)
    [vor-claim 0 (test.root) [first-order (fol-test.signature) []] []
      [[runtime trusted-image]] constructive-first-order
      [derives [[bottom]] [forall person [equal person [v 0] [v 0]]]] concrete-derivation]
    (fol-test.envelope) 20)
  [rejected claim-mismatch])

(fol-test.case imp-wrong-consequent [] [] [imp (fol-test.p) (fol-test.q)] [intro [hyp 0]] rejected)
(fol-test.case congruence [] [[equal person (fol-test.a) (fol-test.b)]]
  [equal person [app f [(fol-test.a)]] [app f [(fol-test.b)]]]
  [subst person [equal person [app f [(fol-test.a)]] [app f [[v 0]]]]
    (fol-test.a) (fol-test.b) [hyp 0] [refl]] accepted)
(test.equal typed-fuel-uncertainty
  (vor.fol-typecheck-bounded (fol-test.signature) [] [] [and [top] [top]] [pair [top] [top]] 2)
  [unknown proof-fuel])
(test.equal symbolic-fuel (vor.fol-check (fol-test.signature) [] [] [top] [top] bad) [rejected invalid-proof-fuel])
(define fol-test.big-formula
  0 -> [top]
  N -> [and (fol-test.big-formula (- N 1)) (fol-test.big-formula (- N 1))])
(define fol-test.big-proof
  0 -> [top]
  N -> [pair (fol-test.big-proof (- N 1)) (fol-test.big-proof (- N 1))])
(define fol-test.big-claim
  -> [vor-claim 0 (test.root) [first-order (fol-test.signature) []] [] []
       constructive-first-order [derives [] (fol-test.big-formula 10)] concrete-derivation])
(test.equal bound-typed-uncertainty
  (vor.typecheck-claim (test.root) (fol-test.big-claim)
    [vor-evidence 0 (fol-test.big-claim) (fol-test.big-proof 10)])
  [unknown proof-fuel])

(load "examples/first-order.shen")
(test.equal quantified-implication-distribution (fol-demo.check) [accepted first-order-derivation])
(test.equal quantified-typed-distribution (fol-demo.typed) [accepted first-order-typed-evidence])
(test.equal quantified-proof-exact-budget
  (vor.fol-check (fol-demo.signature) [] [] (fol-demo.theorem) (fol-demo.proof) 7) [unknown proof-fuel])
(test.equal root-rule-names-unique (vor.unique? (hd (tl (tl (vor.fol-root-inventory))))) true)
(test.equal malformed-annotation
  (vor.fol-check (fol-test.signature) [] [] [top] [fst [pred p [[v 0]]] [hyp 0]] 10)
  [rejected malformed-annotation])
(test.equal scope-invalid-instantiation
  (vor.fol-check (fol-test.signature) [] [] (fol-test.p)
    [inst person [pred p [[v 1]]] (fol-test.a) [hyp 0]] 10)
  [rejected invalid-instantiation])
