\\ R01 hostile corpus: structural binding is checked, not self-reported.
(define test.root -> [vor-root 0 "vor/0-reviewed" "chez-43.1-pr117"])
(define test.claim
  -> [vor-claim 0 (test.root) [model (mutex.model)]
       [[application [model (mutex.model)]]] [[runtime trusted-image]]
       boolean-states [invariant] finite-proof])
(define test.artifact -> [vor-evidence 0 (test.claim) (value *test-cert*)])
(define test.check C A -> (vor.check-claim (test.root) C A 30))

(test.equal claim-valid (vor.claim? (test.claim)) true)
(test.equal claim-checked (test.check (test.claim) (test.artifact))
  [checked (test.claim) [accepted finite-invariant 3]])
(test.equal root-mismatch
  (vor.check-claim [vor-root 0 "other-rules" "chez-43.1-pr117"] (test.claim) (test.artifact) 30)
  [rejected root-mismatch])
(test.equal forged-result (test.check (test.claim)
  [vor-evidence 0 (test.claim) [accepted finite-invariant 3]])
  [rejected certificate-model-or-version-mismatch])
(test.equal empty-certificate (test.check (test.claim)
  [vor-evidence 0 (test.claim) [vor-certificate 0 (mutex.model) []]])
  [rejected missing-initial-state])
(test.equal missing-edge (test.check (test.claim)
  [vor-evidence 0 (test.claim) [vor-certificate 0 (mutex.model) [[false false]]]])
  [rejected not-closed-or-unsafe])
(test.equal changed-payload (test.check (test.claim)
  [vor-evidence 0 (test.claim) [vor-certificate 0 (mutex.broken) [[false false]]]])
  [rejected certificate-model-or-version-mismatch])
(test.equal wrong-envelope-version (test.check (test.claim) [vor-evidence 1 (test.claim) []])
  [rejected malformed-artifact])
(test.equal extra-envelope-field (test.check (test.claim) [vor-evidence 0 (test.claim) [] true])
  [rejected malformed-artifact])
(test.equal claim-is-not-generic-proof (vor.claim?
  [vor-claim 0 (test.root) [model (mutex.model)] [] [] boolean-states [invariant] generic-proof]) false)
(test.equal no-unmodeled-source (vor.claim?
  [vor-claim 0 (test.root) [source [define f X -> X]] [] [] boolean-states [invariant] finite-proof]) false)
(test.equal malformed-bindings (vor.claim?
  [vor-claim 0 (test.root) logic [[a ok] bad] [] intuitionistic-propositions
    [derives empty [truth]] concrete-derivation]) false)
(test.equal duplicate-bindings (vor.claim?
  [vor-claim 0 (test.root) logic [[a ok] [a other]] [] intuitionistic-propositions
    [derives empty [truth]] concrete-derivation]) false)
(test.equal wrong-proof-kind (vor.claim?
  [vor-claim 0 (test.root) logic [] [] intuitionistic-propositions
    [derives empty [truth]] finite-proof]) false)
(test.equal root-needs-identity (vor.root? [vor-root 0 "" "host"]) false)
(test.equal opaque-executable (vor.data? (/. X X)) false)
(test.equal improper-metadata (vor.data? [x | garbage]) false)
(test.equal assumption-extraction (vor.claim-assumptions (test.claim)) [[runtime trusted-image]])

\\ Mutate each claim field independently under an otherwise valid witness.
(define test.substitution
  Name Claim -> (test.equal Name (test.check Claim (test.artifact)) [rejected claim-mismatch]))
(test.substitution changed-model
  [vor-claim 0 (test.root) [model (mutex.broken)]
    [[application [model (mutex.model)]]] [[runtime trusted-image]] boolean-states [invariant] finite-proof])
(test.substitution changed-dependency
  [vor-claim 0 (test.root) [model (mutex.model)]
    [[application [model (mutex.broken)]]] [[runtime trusted-image]] boolean-states [invariant] finite-proof])
(test.substitution removed-assumption
  [vor-claim 0 (test.root) [model (mutex.model)]
    [[application [model (mutex.model)]]] [] boolean-states [invariant] finite-proof])
(test.substitution changed-assumption
  [vor-claim 0 (test.root) [model (mutex.model)]
    [[application [model (mutex.model)]]] [[runtime new-host]] boolean-states [invariant] finite-proof])
(test.substitution changed-judgment
  [vor-claim 0 (test.root) [model (mutex.model)]
    [[application [model (mutex.model)]]] [[runtime trusted-image]]
    boolean-states [trace-prefix [[initial [false false]]]] trace-check])

(define test.logic-claim
  -> [vor-claim 0 (test.root) logic [] [[runtime trusted-image]]
       intuitionistic-propositions [derives empty [implies [atom p] [atom p]]] concrete-derivation])
(test.equal bound-logic
  (test.check (test.logic-claim) [vor-evidence 0 (test.logic-claim) [intro [hyp]]])
  [checked (test.logic-claim) [accepted derivation]])
(test.equal proof-budget
  (vor.check-claim (test.root) (test.logic-claim)
    [vor-evidence 0 (test.logic-claim) [intro [hyp]]] 1)
  [unknown proof-depth])
(test.equal no-admit-claim
  (test.check (test.logic-claim) [vor-evidence 0 (test.logic-claim) [admit]])
  [rejected invalid-proof])
(test.equal negative-proof-budget
  (vor.check-claim (test.root) (test.logic-claim) [] -1) [rejected invalid-budget])

(define test.trace-claim
  -> [vor-claim 0 (test.root) [model (mutex.model)] [] [] boolean-states
       [trace-prefix [[initial [false false]] [step alice-enter [true false]]]] trace-check])
(test.equal bound-trace
  (test.check (test.trace-claim) [vor-evidence 0 (test.trace-claim)
    [[initial [false false]] [step alice-enter [true false]]]])
  [checked (test.trace-claim) [accepted trace-prefix 2]])
(test.equal shorter-trace-is-different-claim
  (test.check (test.trace-claim) [vor-evidence 0 (test.trace-claim) [[initial [false false]]]])
  [rejected trace-mismatch])

(test.equal typed-claim
  (vor.typecheck-claim (test.root) (test.logic-claim)
    [vor-evidence 0 (test.logic-claim) [intro [hyp]]])
  [checked (test.logic-claim) [accepted typed-evidence]])
(test.equal typed-substitution
  (vor.typecheck-claim (test.root) (test.logic-claim) (test.artifact))
  [rejected invalid-evidence])
(test.equal typed-injection
  (vor.typecheck-claim (test.root) (test.logic-claim) [simple-error "never execute"])
  [rejected invalid-evidence])
(test.equal literal-injection (vor.decode-claim-literal [simple-error "never execute"])
  [rejected nonliteral])
