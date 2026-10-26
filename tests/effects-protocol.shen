(load "vor.shen")
(load "examples/effects-protocol.shen")
(define test.equal
  Name Actual Expected -> (if (= Actual Expected) passed (error "effects protocol test failed")))
(define test.counterexample? [counterexample _] -> true _ -> false)
(define test.ok? [ok _] -> true _ -> false)
(test.equal healthy (vor.verify (effects.model) 2048) [accepted finite-invariant 17])
(test.equal commit-mutant (test.counterexample? (vor.verify (effects.mutant-commit) 2048)) true)
(test.equal finish-mutant (test.counterexample? (vor.verify (effects.mutant-finish) 2048)) true)
(test.equal duplicate-mutant (test.counterexample? (vor.verify (effects.mutant-duplicate) 2048)) true)
\\ response is permitted before completion and after completion
(test.equal response-before (test.ok? (vor.next (effects.model) [true true true false false false false false false false])) true)
(test.equal response-after (test.ok? (vor.next (effects.model) [true true false true false false true true true false])) true)
\\ malformed traces and forged certificates are rejected
(test.equal malformed (vor.trace (effects.model) [[initial [false]]]) [rejected invalid-initial-state])
(test.equal forged (vor.check-certificate (effects.model) [accepted finite-invariant 13])
  [rejected certificate-model-or-version-mismatch])
(print effects-protocol-pass)
