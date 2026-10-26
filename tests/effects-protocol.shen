(load "vor.shen")
(load "examples/effects-protocol.shen")
(set *effects-tests* 0)
(define effects-test.equal
  Name Actual Expected ->
    (if (= Actual Expected) (set *effects-tests* (+ 1 (value *effects-tests*)))
        (error "effects protocol ~A: expected ~A, got ~A" Name Expected Actual)))
(define effects-test.violation? [violation invariant _ _] -> true _ -> false)
(define effects-test.recheck
  Model [counterexample Trace] -> (effects-test.violation? (vor.trace Model Trace))
  _ _ -> false)
(define effects-test.certificate [certificate Certificate] -> Certificate)
(effects-test.equal healthy (vor.verify (effects.model) 2048) [accepted finite-invariant 15])
(effects-test.equal budget (vor.verify (effects.model) 1) [unknown state-budget])
(effects-test.equal commit-mutant (effects-test.recheck (effects.mutant-commit) (vor.verify (effects.mutant-commit) 2048)) true)
(effects-test.equal finish-mutant (effects-test.recheck (effects.mutant-finish) (vor.verify (effects.mutant-finish) 2048)) true)
(effects-test.equal duplicate-mutant (effects-test.recheck (effects.mutant-duplicate) (vor.verify (effects.mutant-duplicate) 2048)) true)
(effects-test.equal lost-work-mutant (effects-test.recheck (effects.mutant-lost-work) (vor.verify (effects.mutant-lost-work) 2048)) true)
\\ All events here are explicit abstract protocol transitions, not SUT evidence.
(effects-test.equal recovery-trace
(vor.trace (effects.model)
 [[initial [false false false false false false false false false false]]
  [step request-commit [true true true false false false false false false false]]
  [step respond [true true true true false false false false false false]]
  [step claim [true true true true true false false false false false]]
  [step apply-effect [true true true true true false true false false false]]
  [step lose-ack [true true true true true false true false false false]]
  [step crash [true true true true false true true false false false]]
  [step claim [true true true true true false true false false false]]
  [step apply-effect [true true true true true false true false false false]]
  [step acknowledge [true true true true true false true true false false]]
  [step finish [true true false true false false true true true false]]])
[accepted trace-prefix 11])
(effects-test.equal response-after-completion
(vor.trace (effects.model)
 [[initial [false false false false false false false false false false]]
  [step request-commit [true true true false false false false false false false]]
  [step claim [true true true false true false false false false false]]
  [step apply-effect [true true true false true false true false false false]]
  [step acknowledge [true true true false true false true true false false]]
  [step finish [true true false false false false true true true false]]
  [step respond [true true false true false false true true true false]]])
[accepted trace-prefix 7])
(effects-test.equal malformed (vor.trace (effects.model) [[initial [false]]]) [rejected invalid-initial-state])
(effects-test.equal forged (vor.check-certificate (effects.model) [accepted finite-invariant 15]) [rejected certificate-model-or-version-mismatch])
(effects-test.equal mismatched-model
(vor.check-certificate (effects.mutant-commit) (effects-test.certificate (vor.explore (effects.model) 2048)))
[rejected certificate-model-or-version-mismatch])
(print [effects-protocol-pass (value *effects-tests*)])
