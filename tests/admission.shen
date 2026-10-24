(tc -)
(load "examples/admission.shen")
(test.equal admission-domain
  (vor.admission-domain? (admission-demo.program) (admission-demo.signature) (admission-demo.contracts)) true)
(test.equal construction-checked (hd (vor.construct-check (admission-demo.program)
  (admission-demo.signature) (admission-demo.contracts) (admission-demo.construction))) constructed)
(test.equal generic-admission (admission-demo.check) [accepted total-admission])
(test.equal generic-admission-indexed
  (vor.admission-typecheck (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) 2000) [accepted typed-admission])
(test.equal admission-no-fuel
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) 0) [unknown proof-fuel])
(test.equal admission-shared-fuel
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) 3) [unknown proof-fuel])
(test.equal admission-no-invalid-fuel
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) 65536) [rejected invalid-proof-fuel])
(test.equal admission-no-flag
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) true 2000) [rejected admission-identity])
(test.equal admission-no-executable-evidence
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) [simple-error "never execute"] 2000) [rejected admission-identity])
(test.equal admission-no-missing-posts
  (vor.admit (admission-demo.program) (admission-demo.signature) (admission-demo.contracts)
    [vor-admission 0 (admission-demo.program) (admission-demo.signature)
      (admission-demo.contracts) (admission-demo.construction) []] 2000)
  [rejected contract-proof-coverage])
(test.equal admission-no-missing-definitions
  (vor.construct-check (admission-demo.program) (admission-demo.signature) (admission-demo.contracts) [])
  [rejected construction-definitions])
(test.equal admission-no-forged-construction
  (hd (vor.construct-check (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) [[definition total.add [[case zero [top]] [case succ [top]]]]])) rejected)
(test.equal admission-no-foreign-axioms
  (vor.contracts? [fol-signature 1 [] (append (vor.contract-functions (admission-demo.contracts))
       [[foreign.oracle [natural] natural]]) [] (vor.standard-data)] (admission-demo.contracts)) false)
(test.equal admission-no-out-of-domain-precondition
  (vor.contracts? (admission-demo.signature)
    [[contract total.add [natural natural] natural 0 [pred hidden-precondition [[v 1]]]]]) false)
(test.equal admission-no-empty-input-measure
  (vor.contracts? [fol-signature 1 [] [[constant [] natural]] [] (vor.standard-data)]
    [[contract constant [] natural 0 [top]]]) false)
(test.equal admission-no-measure-out-of-range
  (vor.contracts? [fol-signature 1 [] [[identity [natural] natural]] [] (vor.standard-data)]
    [[contract identity [natural] natural 1 [top]]]) false)

\\ Mutants rebind the whole program/evidence envelope, so a mere outer identity
\\ mismatch cannot explain rejection. The construction or generic proof fails.
(define admit-test.replace
  T A B -> B where (= T A)
  [H | T] A B -> [(admit-test.replace H A B) | (admit-test.replace T A B)]
  T _ _ -> T)
(define admit-test.mutant
  A B -> (admission-demo.normalized (vor.normalize (admit-test.replace (admission-demo.source) A B))))
(define admit-test.recheck
  P -> (vor.admit P (admission-demo.signature) (admission-demo.contracts)
    [vor-admission 0 P (admission-demo.signature) (admission-demo.contracts)
      (vor.construct P (admission-demo.signature) (admission-demo.contracts)) (admission-demo.posts)] 2000))
(define admit-test.x -> (intern "X"))
(define admit-test.y -> (intern "Y"))
(define admit-test.h -> (intern "H"))
(define admit-test.t -> (intern "T"))
(test.equal admission-no-nondecreasing-recursion
  (admit-test.recheck (admit-test.mutant [total.copy (admit-test.x)]
    [total.copy [cons succ [cons (admit-test.x) []]]]))
  [rejected nondecreasing-recursion])
(test.equal admission-no-unrelated-smaller-witness
  (admit-test.recheck (admit-test.mutant [total.copy (admit-test.x)] [total.copy zero]))
  [rejected nondecreasing-recursion])
(test.equal admission-changed-parameters-requires-new-generic-proof
  (hd (admit-test.recheck (admit-test.mutant [total.add (admit-test.x) (admit-test.y)]
    [total.add (admit-test.x) zero]))) rejected)
(test.equal admission-no-future-call
  (admit-test.recheck (admit-test.mutant [total.copy (admit-test.x)] [total.twice (admit-test.x)]))
  [rejected unadmitted-call])
(test.equal admission-no-right-shape-wrong-value
  (hd (admit-test.recheck (admit-test.mutant
    [cons succ [cons [total.copy (admit-test.x)] []]] zero))) rejected)
(test.equal admission-no-omitted-list-element
  (hd (admit-test.recheck (admit-test.mutant
    [cons cell [cons (admit-test.h) [cons [total.append (admit-test.t) (admit-test.y)] []]]]
    [total.append (admit-test.t) (admit-test.y)]))) rejected)
(test.equal admission-no-wrong-constructor-sort
  (hd (admit-test.recheck (admit-test.mutant
    [cons succ [cons [total.copy (admit-test.x)] []]]
    [cons cell [cons zero [cons nil []]]]))) rejected)
(test.equal admission-no-coverage-gap
  (hd (admit-test.recheck (admit-test.mutant
    [define total.copy zero -> zero
      [cons succ [cons (admit-test.x) []]] -> [cons succ [cons [total.copy (admit-test.x)] []]]]
    [define total.copy zero -> zero]))) rejected)
(test.equal admission-no-failing-guard
  (hd (admit-test.recheck (admit-test.mutant
    [define total.copy zero -> zero
      [cons succ [cons (admit-test.x) []]] -> [cons succ [cons [total.copy (admit-test.x)] []]]]
    [define total.copy zero -> zero where false
      [cons succ [cons (admit-test.x) []]] -> [cons succ [cons [total.copy (admit-test.x)] []]]]))) rejected)
(test.equal admission-no-nonlinear-pattern
  (hd (admit-test.recheck (admit-test.mutant
    [define total.add zero (admit-test.y) -> (admit-test.y)
      [cons succ [cons (admit-test.x) []]] (admit-test.y) ->
        [cons succ [cons [total.add (admit-test.x) (admit-test.y)] []]]]
    [define total.add zero (admit-test.y) -> (admit-test.y)
      [cons succ [cons (admit-test.x) []]] (admit-test.x) ->
        [cons succ [cons [total.add (admit-test.x) (admit-test.x)] []]]]))) rejected)

(define admit-test.associativity
  -> [forall natural [forall natural [forall natural
    [equal natural [app total.add [[app total.add [[v 0] [v 1]]] [v 2]]]
      [app total.add [[v 0] [app total.add [[v 1] [v 2]]]]]]]]])
(test.equal generic-addition-associativity
  (vor.check-constructed-theorem (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.construction)
    (admit-test.associativity) (admission-demo.associativity) 2000)
  [accepted constructed-theorem])
(test.equal generic-append-right-identity
  (vor.check-constructed-theorem (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.construction)
    [forall nat-list [equal nat-list [app total.append [[v 0] [app nil []]]] [v 0]]]
    (admission-demo.append-right-nil) 2000) [accepted constructed-theorem])
(test.equal generic-theorem-no-axiom-flag
  (hd (vor.check-constructed-theorem (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.construction)
    [forall natural [equal natural [v 0] [app zero []]]] [verified true] 2000)) rejected)
(test.equal generic-theorem-no-circular-definition
  (hd (vor.check-constructed-theorem
    (admit-test.mutant [total.copy (admit-test.x)] [total.copy [cons succ [cons (admit-test.x) []]]])
    (admission-demo.signature) (admission-demo.contracts) (admission-demo.construction)
    [bottom] [hyp 0] 2000)) rejected)
(test.equal composition-generic-derivation
  (vor.fol-check [fol-signature 1 [] [] [[p [natural]] [q [natural]] [r [natural]]] (vor.standard-data)]
    [] [] [forall natural [imp [imp [pred p [[v 0]]] [pred q [[v 0]]]]
      [imp [imp [pred q [[v 0]]] [pred r [[v 0]]]] [imp [pred p [[v 0]]] [pred r [[v 0]]]]]]]
    (vor.composition-proof [pred p [[v 0]]] [pred q [[v 0]]]) 10)
  [accepted first-order-derivation])

(define admit-test.outcome
  [executed-admitted Outcome _] -> Outcome
  R -> R)
(test.equal admitted-exec-composed
  (admit-test.outcome (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) total.twice [[succ [succ zero]]] 2000 1000))
  [value [succ [succ [succ [succ zero]]]]])
(test.equal admitted-exec-append
  (admit-test.outcome (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) total.append
    [[cell zero [cell [succ zero] nil]] [cell [succ [succ zero]] nil]] 2000 1000))
  [value [cell zero [cell [succ zero] [cell [succ [succ zero]] nil]]]])
(test.equal admitted-exec-domain
  (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) total.copy [3] 2000 1000)
  [rejected input-outside-contract])
(test.equal admitted-exec-still-budgeted
  (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) total.copy [[succ zero]] 2000 1)
  [unknown evaluation-fuel])
(test.equal admitted-exec-rechecks-admission
  (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) true total.copy [zero] 2000 1000) [rejected admission-identity])

(define admit-test.claim
  -> [vor-claim 0 (test.root)
    [total-program (admission-demo.program) (admission-demo.signature) (admission-demo.contracts)]
    [] [[runtime trusted-image] [root positive-initial-algebras]] total-shen-1 [total-contracts] generic-proof])
(define admit-test.envelope -> [vor-evidence 0 (admit-test.claim) (admission-demo.evidence)])
(test.equal admission-bound-generic
  (vor.check-claim (test.root) (admit-test.claim) (admit-test.envelope) 2000)
  [checked (admit-test.claim) [accepted total-admission]])
(test.equal admission-bound-indexed
  (vor.typecheck-claim (test.root) (admit-test.claim) (admit-test.envelope))
  [checked (admit-test.claim) [accepted typed-evidence]])
(test.equal admission-bound-wire
  (vor.check-artifact (test.root) (admit-test.claim)
    (test.ok (vor.pack (admit-test.envelope) 1048576 256 65536)) 1048576 256 65536 2000)
  [checked (admit-test.claim) [accepted total-admission]])
(test.equal admission-no-contract-substitution
  (vor.admit (admission-demo.program) (admission-demo.signature)
    (tl (admission-demo.contracts)) (admission-demo.evidence) 2000) [rejected admission-identity])
(test.equal admission-no-source-substitution
  (vor.admit (admit-test.mutant [total.copy (admit-test.x)] [total.copy zero])
    (admission-demo.signature) (admission-demo.contracts) (admission-demo.evidence) 2000)
  [rejected admission-identity])

\\ Test-only numeric oracle: running the exact admitted code agrees with the
\\ independent host operation on 81 bounded pairs. Generic proofs above do
\\ not depend on this test corpus or data-test.peano.
(define admit-test.add-row
  _ 9 -> done
  A B -> (do
    (test.equal admitted-add-reference
      (admit-test.outcome (vor.run-admitted (admission-demo.program) (admission-demo.signature)
        (admission-demo.contracts) (admission-demo.evidence) total.add
        [(data-test.peano A) (data-test.peano B)] 2000 2000))
      [value (data-test.peano (+ A B))])
    (admit-test.add-row A (+ B 1))))
(define admit-test.add-grid
  9 -> done
  A -> (do (admit-test.add-row A 0) (admit-test.add-grid (+ A 1))))
(admit-test.add-grid 0)
(define admit-test.theorem-claim
  -> [vor-claim 0 (test.root)
    [total-program (admission-demo.program) (admission-demo.signature) (admission-demo.contracts)]
    [] [[runtime trusted-image]] total-shen-1 [theorem (admit-test.associativity)] generic-proof])
(define admit-test.theorem-envelope
  -> [vor-evidence 0 (admit-test.theorem-claim)
       [constructed-theorem 0 (admission-demo.construction) (admission-demo.associativity)]])
(test.equal generic-theorem-bound
  (vor.check-claim (test.root) (admit-test.theorem-claim) (admit-test.theorem-envelope) 2000)
  [checked (admit-test.theorem-claim) [accepted constructed-theorem]])
(test.equal generic-theorem-wire
  (vor.check-artifact (test.root) (admit-test.theorem-claim)
    (test.ok (vor.pack (admit-test.theorem-envelope) 1048576 256 65536)) 1048576 256 65536 2000)
  [checked (admit-test.theorem-claim) [accepted constructed-theorem]])
(test.equal generic-theorem-missing-construction
  (hd (vor.check-claim (test.root) (admit-test.theorem-claim)
    [vor-evidence 0 (admit-test.theorem-claim) [constructed-theorem 0 [] [hyp 0]]] 2000)) rejected)
(test.equal generic-theorem-no-context-smuggling
  (vor.check-claim (test.root) (admit-test.theorem-claim)
    [vor-evidence 0 (admit-test.theorem-claim)
      [constructed-theorem 0 (admission-demo.construction) [[bottom]] [hyp 0]]] 2000)
  [rejected unsupported-claim-evidence])
(define admit-test.nonlinear-source
  -> [shen-source 0 [[define nonlinear zero (admit-test.y) -> zero
    [cons succ [cons (admit-test.x) []]] (admit-test.x) -> zero]]])
(define admit-test.nonlinear-program
  -> (admission-demo.normalized (vor.normalize (admit-test.nonlinear-source))))
(define admit-test.nonlinear-contracts
  -> [[contract nonlinear [natural natural] natural 0 [top]]])
(define admit-test.nonlinear-signature
  -> [fol-signature 1 [] (vor.contract-functions (admit-test.nonlinear-contracts)) [] (vor.standard-data)])
(test.equal construction-linearity-independent-of-post
  (vor.construct-check (admit-test.nonlinear-program) (admit-test.nonlinear-signature)
    (admit-test.nonlinear-contracts)
    (vor.construct (admit-test.nonlinear-program) (admit-test.nonlinear-signature) (admit-test.nonlinear-contracts)))
  [rejected nonlinear-pattern])
(test.equal construction-decrease-independent-of-post
  (let P (admit-test.mutant [total.copy (admit-test.x)] [total.copy [cons succ [cons (admit-test.x) []]]])
    (vor.construct-check P (admission-demo.signature) (admission-demo.contracts)
      (vor.construct P (admission-demo.signature) (admission-demo.contracts))))
  [rejected nondecreasing-recursion])
(test.equal admission-no-unencoded-tree-field
  (vor.contracts? [fol-signature 1 [] [[wrap-id [wrapper] wrapper]] []
    [[data wrapper [[wrap [vor.tree]]]]]] [[contract wrap-id [wrapper] wrapper 0 [top]]]) false)

(test.equal admission-root-inventory
  (hd (vor.construction-root-inventory)) vor-construction-root)

(test.equal construction-changing-typed-parameters
  (let P (admit-test.mutant [total.add (admit-test.x) (admit-test.y)] [total.add (admit-test.x) zero])
    (hd (vor.construct-check P (admission-demo.signature) (admission-demo.contracts)
      (vor.construct P (admission-demo.signature) (admission-demo.contracts))))) constructed)
(test.equal generic-accumulator-reversal-admission
  (admission-demo.check) [accepted total-admission])
(test.equal accumulator-reversal-exact-ground-value
  (admit-test.outcome (vor.run-admitted (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.evidence) total.reverse
    [[cell zero [cell [succ zero] nil]] [cell [succ [succ zero]] nil]] 2000 2000))
  [value [cell [succ zero] [cell zero [cell [succ [succ zero]] nil]]]])
(test.equal generic-addition-right-successor
  (vor.check-constructed-theorem (admission-demo.program) (admission-demo.signature)
    (admission-demo.contracts) (admission-demo.construction)
    (admission-demo.right-succ) (admission-demo.right-succ-proof) 2000)
  [accepted constructed-theorem])
