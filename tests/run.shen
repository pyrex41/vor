(load "vor.shen")
(load "examples/mutex.shen")
(set *vor-test-count* 0)
(maxinferences 10000000)

(define test.equal
  Name Actual Expected ->
    (if (= Actual Expected)
        (do (set *vor-test-count* (+ 1 (value *vor-test-count*))) passed)
        (error "~A: expected ~A, got ~A" Name Expected Actual)))

\\ Ask System S itself; (type ...) with tc- would not be a checking oracle.
(define test.typed?
  Evidence Judgment ->
    (let Term (shen.curry (shen.rcons_form Evidence))
      Sequent [Term : Judgment]
      (prolog? (shen.system-S (receive Sequent) []))))

(test.equal valid-model (vor.model? (mutex.model)) true)
(test.equal finite-proof (vor.verify (mutex.model) 4) [accepted finite-invariant 3])
(test.equal exact-budget (vor.verify (mutex.model) 3) [accepted finite-invariant 3])
(test.equal exhausted (vor.verify (mutex.model) 2) [unknown state-budget])
(test.equal zero-budget (vor.verify (mutex.model) 0) [rejected invalid-budget])
(test.equal fractional-budget (vor.verify (mutex.model) 0.5) [rejected invalid-budget])
(test.equal symbolic-budget (vor.verify (mutex.model) bad) [rejected invalid-budget])
(test.equal broken (vor.verify (mutex.broken) 4)
  [counterexample [[initial [false false]] [step alice-enter [true false]] [step bob-enter [true true]]]])
(test.equal initial-violation
  (vor.verify [vor-model 0 [x] [[true]] [] [neg [var x]]] 1)
  [counterexample [[initial [true]]]])
(test.equal deadlock-is-not-liveness
  (vor.verify [vor-model 0 [] [[]] [] [lit true]] 1)
  [accepted finite-invariant 1])
(test.equal reject-unknown-version (vor.model? [vor-model 1 [] [[]] [] [lit true]]) false)
(test.equal reject-empty-initial (vor.model? [vor-model 0 [] [] [] [lit true]]) false)
(test.equal reject-duplicate-variable
  (vor.model? [vor-model 0 [x x] [[false false]] [] [lit true]]) false)
(test.equal reject-bad-state (vor.model? [vor-model 0 [x] [[1]] [] [lit true]]) false)
(test.equal reject-improper-state (vor.model? [vor-model 0 [x] [[true | bad]] [] [lit true]]) false)
(test.equal reject-duplicate-initial (vor.model? [vor-model 0 [x] [[true] [true]] [] [lit true]]) false)
(test.equal reject-unknown-variable (vor.model? [vor-model 0 [] [[]] [] [var x]]) false)
(test.equal reject-host-code (vor.model? [vor-model 0 [] [[]] [] [eval [simple-error bad]]]) false)
(test.equal reject-bad-assignment
  (vor.model? [vor-model 0 [x] [[false]] [[rule a [lit true] [[y [lit true]]]]] [lit true]]) false)
(test.equal reject-duplicate-write
  (vor.model? [vor-model 0 [x] [[false]] [[rule a [lit true] [[x [lit true]] [x [lit false]]]]] [lit true]]) false)
(test.equal reject-duplicate-label
  (vor.model? [vor-model 0 [] [[]] [[rule a [lit true] []] [rule a [lit false] []]] [lit true]]) false)
(test.equal reject-extra-model-fields (vor.model? [vor-model 0 [] [[]] [] [lit true] junk]) false)
(test.equal reject-malformed-next (vor.next bad []) [rejected invalid-model])
(test.equal reject-invalid-state (vor.next (mutex.model) [1 2]) [rejected invalid-state])

\\ Simultaneous assignments must swap, not overwrite both with the first value.
(test.equal simultaneous
  (vor.next [vor-model 0 [x y] [[true false]]
              [[rule swap [lit true] [[x [var y]] [y [var x]]]]] [lit true]]
            [true false])
  [ok [[step swap [false true]]]])

(define test.cert
  [certificate C] -> C
  _ -> (simple-error "expected certificate"))
(set *test-cert* (test.cert (vor.explore (mutex.model) 4)))
(test.equal certificate (vor.check-certificate (mutex.model) (value *test-cert*)) [accepted finite-invariant 3])
(test.equal missing-initial
  (vor.check-certificate (mutex.model) [vor-certificate 0 (mutex.model) [[true false]]])
  [rejected missing-initial-state])
(test.equal missing-successor
  (vor.check-certificate (mutex.model) [vor-certificate 0 (mutex.model) [[false false]]])
  [rejected not-closed-or-unsafe])
(test.equal unsafe-added
  (vor.check-certificate (mutex.model)
    [vor-certificate 0 (mutex.model) [[false false] [true false] [false true] [true true]]])
  [rejected not-closed-or-unsafe])
(test.equal duplicate-certificate
  (vor.check-certificate (mutex.model) [vor-certificate 0 (mutex.model) [[false false] [false false]]])
  [rejected invalid-state-set])
(test.equal stale-model (vor.check-certificate (mutex.broken) (value *test-cert*))
  [rejected certificate-model-or-version-mismatch])
(test.equal forged-acceptance (vor.check-certificate (mutex.model) [accepted finite-invariant 3])
  [rejected certificate-model-or-version-mismatch])

(test.equal trace (vor.trace (mutex.model) [[initial [false false]] [step alice-enter [true false]]])
  [accepted trace-prefix 2])
(test.equal trace-wrong-label (vor.trace (mutex.model) [[initial [false false]] [step bob-enter [true false]]])
  [rejected illegal-step 1])
(test.equal trace-implicit-stutter (vor.trace (mutex.model) [[initial [false false]] [step stutter [false false]]])
  [rejected illegal-step 1])
(test.equal trace-empty (vor.trace (mutex.model) []) [rejected invalid-trace])
(test.equal trace-unreachable-start (vor.trace (mutex.model) [[initial [true false]]])
  [rejected invalid-initial-state])
(test.equal trace-bad-tail (vor.trace (mutex.model) [[initial [false false]] | bad])
  [rejected malformed-trace 1])
(test.equal trace-counterexample
  (vor.trace (mutex.broken) [[initial [false false]] [step alice-enter [true false]] [step bob-enter [true true]]])
  [violation invariant 2 [true true]])

\\ Both checking routes consume inert proof objects, including hostile ones.
(define test.context
  [] -> empty
  [P | Ps] -> [assuming P (test.context Ps)])

(define test.proof-case
  Name G P D Expected ->
    (do (test.equal Name (= (vor.proof (test.context G) P D 30) [accepted derivation]) Expected)
        (test.equal Name (test.typed? D [vor-proves (test.context G) P]) Expected)))

(test.proof-case identity [] [implies [atom p] [atom p]] [intro [hyp]] true)
(test.proof-case no-assumption [] [atom p] [hyp] false)
(test.proof-case truth [] [truth] [unit] true)
(test.proof-case no-admit [] [falsehood] [admit] false)
(test.proof-case conjunction [[atom p] [atom q]] [both [atom p] [atom q]] [pair [hyp] [hyp]] true)
(test.proof-case projection [[both [atom p] [atom q]]] [atom p] [left [atom q] [hyp]] true)
(test.proof-case right-projection [[both [atom p] [atom q]]] [atom q] [right [atom p] [hyp]] true)
(test.proof-case modus-ponens [[implies [atom p] [atom q]] [atom p]] [atom q]
  [apply [atom p] [hyp] [hyp]] true)
(test.proof-case invalid-application [[implies [atom p] [atom q]]] [atom q]
  [apply [atom p] [hyp] [unit]] false)
(test.proof-case explosion [[falsehood]] [atom p] [absurd [hyp]] true)
(test.proof-case forged-explosion [] [atom p] [absurd [unit]] false)
(test.proof-case no-classical-axiom [] [atom p] [excluded-middle] false)
(test.proof-case malformed-formula [] [implies junk junk] [intro [hyp]] false)
(test.proof-case malformed-context [junk] [truth] [unit] false)
(test.proof-case no-assumption-leak [] [both [implies [atom p] [atom p]] [atom p]]
  [pair [intro [hyp]] [hyp]] false)
(test.equal proof-exhaustion (vor.proof empty [implies [atom p] [atom p]] [intro [hyp]] 1)
  [unknown proof-depth])
(test.equal proof-malformed-budget (vor.proof empty [truth] [unit] -1) [rejected invalid-budget])
(test.equal typed-step
  (test.typed? [step alice-enter [true false]] [vor-step (mutex.model) [false false] alice-enter [true false]]) true)
(test.equal typed-forged-step
  (test.typed? [step alice-enter [true true]] [vor-step (mutex.model) [false false] alice-enter [true true]]) false)
(test.equal typed-initial (test.typed? [initial [false false]] [vor-initial (mutex.model) [false false]]) true)
(test.equal typed-unsafe (test.typed? [safe [true true]] [vor-safe (mutex.model) [true true]]) false)
(test.equal public-typecheck
  (vor.typecheck [intro [hyp]] [vor-proves empty [implies [atom p] [atom p]]])
  [accepted typed-evidence])
(test.equal public-typecheck-rejects
  (vor.typecheck [admit] [vor-proves empty [falsehood]]) [rejected invalid-evidence])
(test.equal public-typecheck-domain
  (vor.typecheck [unit] [list number]) [rejected malformed-judgment])
(test.equal no-executable-proof
  (vor.typecheck [simple-error "do not execute"] [vor-proves empty [truth]])
  [rejected invalid-evidence])
(test.equal no-executable-annotation
  (vor.decode-literal [simple-error "do not execute"]) [rejected nonliteral])

(define test.observer-model
  -> [vor-model 0 [x y] [[false false] [false true]]
       [[rule flip [lit true] [[x [neg [var x]]]]]] [lit true]])
(test.equal preserve-ambiguity
  (vor.observe (test.observer-model) [[false false] [false true]] flip [[x true]] 2)
  [consistent [[true true] [true false]]])
(test.equal observed-narrowing
  (vor.observe (test.observer-model) [[false false] [false true]] flip [[y false]] 2)
  [consistent [[true false]]])
(test.equal forbidden-observation
  (vor.observe (test.observer-model) [[false false] [false true]] flip [[x false]] 2)
  [violation forbidden-observation])
(test.equal belief-budget
  (vor.observe (test.observer-model) [[false false] [false true]] flip [] 1)
  [unknown state-budget])
(test.equal empty-belief (vor.observe (test.observer-model) [] flip [] 2) [rejected invalid-belief-set])
(test.equal malformed-observation
  (vor.observe (test.observer-model) [[false false]] flip [[z true]] 2)
  [rejected malformed-observation])
(test.equal duplicate-observation
  (vor.observe (test.observer-model) [[false false]] flip [[x true] [x true]] 2)
  [rejected duplicate-observation-field])

(load "tests/exhaustive.shen")
(load "tests/roadmap.shen")
(load "tests/claim-binding.shen")
(load "tests/artifact.shen")
(load "tests/artifact-known.shen")
(load "tests/program.shen")
(load "tests/program-native.shen")
(load "tests/assumption-boundaries.shen")
(load "tests/first-order.shen")
(load "tests/first-order-reference.shen")
(load "tests/first-order-kripke.shen")
(output "VOR: ~A checks passed.~%" (value *vor-test-count*))
