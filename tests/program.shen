\\ R03: trusted fixtures only. Acceptance code never invokes eval-kl or load.
(tc -)
(define program-test.source
  Body -> [shen-source 0 [[define r03.entry -> Body]]])
(define program-test.program
  Source -> (test.ok (vor.normalize Source)))
(define program-test.outcome
  [evaluated Outcome _] -> Outcome
  R -> R)
(define program-test.evidence
  [evaluated _ E] -> E
  R -> (error "expected execution witness, got ~A" R))
(define program-test.check
  Name Source Function Args Expected ->
    (let Program (program-test.program Source)
      Run (vor.run Program Function Args 3000)
      (do (test.equal Name (program-test.outcome Run) Expected)
        (test.equal Name (vor.check-evaluation Program Function Args Expected
          (program-test.evidence Run) 3000) [accepted evaluation]))))
(define program-test.closed
  Name Body Expected -> (program-test.check Name (program-test.source Body) r03.entry [] Expected))

(program-test.closed literal 42 [value 42])
(program-test.closed boolean true [value true])
(program-test.closed nil [] [value []])
(program-test.closed text "hello" [value "hello"])
(program-test.closed scalar-symbol example [value example])
(program-test.closed cons [cons 1 []] [value [1]])
(program-test.closed improper-cons [cons 1 2] [value [1 | 2]])
(program-test.closed head [hd [cons a []]] [value a])
(program-test.closed tail [tl [cons a b]] [value b])
(program-test.closed hd-error [hd []] [error [primitive-domain hd]])
(program-test.closed tl-error [tl []] [error [primitive-domain tl]])
(program-test.closed if-lazy [if true good [hd []]] [value good])
(program-test.closed else-lazy [if false [hd []] good] [value good])
(program-test.closed nonboolean-condition [if 0 yes no] [error nonboolean-condition])
(program-test.closed equality [= [cons a b] [cons a b]] [value true])
(program-test.closed protected-symbol [protect (intern "X")] [value (intern "X")])
(program-test.closed left-to-right [cons [hd []] [tl []]] [error [primitive-domain hd]])
(program-test.closed left-to-right-reversed [cons [tl []] [hd []]] [error [primitive-domain tl]])
(program-test.closed let-shadow
  [let (intern "X") outer [let (intern "X") inner (intern "X")]] [value inner])
(program-test.closed let-value-uses-outer
  [let (intern "X") outer [let (intern "X") [cons (intern "X") []] (intern "X")]] [value [outer]])
(program-test.closed let-strict [let (intern "X") [hd []] ignored] [error [primitive-domain hd]])

(define program-test.clauses
  -> (let X (intern "X") Xs (intern "Xs")
    [shen-source 0
      [[define r03.first X -> first _ -> second]
       [define r03.head [] -> empty [cons X Xs] -> X _ -> other]
       [define r03.same X X -> same _ _ -> different]
       [define r03.guarded X -> matched where [= X target] _ -> fallback]
       [define r03.guard-error X -> matched where [hd X] _ -> fallback]
       [define r03.only target -> found]
       [define r03.skip-guard [] -> unreachable where [hd []] _ -> fallback]
       [define r03.append [] X -> X [cons X Xs] (intern "Ys") ->
         [cons X [r03.append Xs (intern "Ys")]]]
       [define r03.diagonal [cons X X] -> matched _ -> different]
       [define r03.guard-loop X -> matched where [r03.loop] _ -> fallback]
       [define r03.even [] -> true [cons _ Xs] -> [r03.odd Xs]]
       [define r03.odd [] -> false [cons _ Xs] -> [r03.even Xs]]
       [define r03.loop -> [r03.loop]]]]))
(program-test.check priority (program-test.clauses) r03.first [anything] [value first])
(program-test.check nil-pattern (program-test.clauses) r03.head [[]] [value empty])
(program-test.check cons-pattern (program-test.clauses) r03.head [[a b]] [value a])
(program-test.check scalar-fallback (program-test.clauses) r03.head [0] [value other])
(program-test.check repeated-true (program-test.clauses) r03.same [[a b] [a b]] [value same])
(program-test.check repeated-false (program-test.clauses) r03.same [[a] [b]] [value different])
(program-test.check guard-true (program-test.clauses) r03.guarded [target] [value matched])
(program-test.check guard-false (program-test.clauses) r03.guarded [other] [value fallback])
(program-test.check guard-error (program-test.clauses) r03.guard-error [[]] [error [primitive-domain hd]])
(program-test.check guard-nonboolean (program-test.clauses) r03.guard-error [[7]] [error nonboolean-guard])
(program-test.check no-clause (program-test.clauses) r03.only [other] [error [no-clause r03.only]])
(program-test.check recursive-append (program-test.clauses) r03.append [[a b] [c d]] [value [a b c d]])
(test.equal recursion-budget
  (vor.run (program-test.program (program-test.clauses)) r03.loop [] 100) [unknown evaluation-fuel])
(test.equal zero-evaluation-budget
  (vor.run (program-test.program (program-test.clauses)) r03.first [a] 0) [unknown evaluation-fuel])
(test.equal invalid-evaluation-budget
  (vor.run (program-test.program (program-test.clauses)) r03.first [a] -1) [rejected invalid-evaluation-fuel])

(test.equal unknown-call (vor.normalize (program-test.source [missing 1])) [rejected unknown-function-or-form])
(test.equal call-arity (vor.normalize (program-test.source [cons 1])) [rejected call-arity])
(test.equal unbound-variable (vor.normalize (program-test.source (intern "X"))) [rejected unbound-variable])
(test.equal no-eval (vor.normalize (program-test.source [eval [cons a []]])) [rejected unknown-function-or-form])
(test.equal no-set (vor.normalize (program-test.source [set sentinel changed])) [rejected unknown-function-or-form])
(test.equal no-lambda (vor.normalize (program-test.source [lambda (intern "X") (intern "X")])) [rejected unknown-function-or-form])
(test.equal no-computed-call (vor.normalize (program-test.source [[protect fn] 0])) [rejected unsupported-application])
(test.equal no-wildcard-body (vor.normalize (program-test.source (intern "_"))) [rejected wildcard-expression])
(test.equal no-primitive-redefinition (vor.normalize [shen-source 0 [[define hd -> forged]]]) [rejected reserved-or-invalid-function])
(test.equal duplicate-definition (vor.normalize [shen-source 0 [[define a -> true] [define a -> false]]]) [rejected duplicate-function])
(test.equal inconsistent-arity (vor.normalize [shen-source 0 [[define a x -> true x y -> false]]]) [rejected inconsistent-clause-arity])
(test.equal unknown-source-version (vor.normalize [shen-source 1 []]) [rejected unsupported-source-version])
(test.equal empty-source (vor.normalize [shen-source 0 []]) [rejected empty-or-improper-source])
(test.equal malformed-pattern (vor.normalize [shen-source 0 [[define a [foo x] -> true]]]) [rejected unsupported-pattern])
(test.equal no-negative-literals (vor.normalize (program-test.source -1)) [rejected unsupported-literal])
(test.equal no-floating-literals (vor.normalize (program-test.source 0.5)) [rejected unsupported-literal])
(test.equal no-large-literals (vor.normalize (program-test.source 65536)) [rejected unsupported-literal])

\\ Rebinding the host's same-spelled name cannot change the closed program.
(define r03.first X -> hostile-global)
(program-test.check closed-resolution (program-test.clauses) r03.first [anything] [value first])
(define r03.first X -> newly-rebound)
(program-test.check closed-rebinding (program-test.clauses) r03.first [anything] [value first])

(define program-test.tamper-program
  [vor-program 0 Source _] -> [vor-program 0 Source [[function r03.entry 0 [[clause [] [literal true] [literal forged]]]]]])
(test.equal altered-normalization
  (vor.program? (program-test.tamper-program (program-test.program (program-test.source good)))) false)
(test.equal check-normalization
  (vor.check-normalization (program-test.source good)
    [vor-normalization 0 (program-test.source good) (program-test.program (program-test.source good))])
  [accepted normalization])
(test.equal reject-normalization-tamper
  (vor.check-normalization (program-test.source good)
    [vor-normalization 0 (program-test.source good)
      (program-test.tamper-program (program-test.program (program-test.source good)))])
  [rejected normalization-mismatch])

(define program-test.p -> (program-test.program (program-test.source good)))
(define program-test.run -> (vor.run (program-test.p) r03.entry [] 100))
(define program-test.trace
  [vor-evaluation 0 _ _ _ _ States] -> States)
(define program-test.with-trace
  States -> [vor-evaluation 0 (program-test.p) r03.entry [] [value good] States])
(define program-test.check-evidence
  E -> (vor.check-evaluation (program-test.p) r03.entry [] [value good] E 100))
(define program-test.drop-last
  [_] -> []
  [X | Xs] -> [X | (program-test.drop-last Xs)])
(test.equal no-forged-result (program-test.check-evidence [accepted evaluation]) [rejected evaluation-identity-mismatch])
(test.equal skipped-step
  (program-test.check-evidence (program-test.with-trace
    [[machine [call r03.entry []] []] [machine [return good] []]])) [rejected illegal-evaluation-step])
(test.equal wrong-initial
  (program-test.check-evidence (program-test.with-trace [[machine [return good] []]])) [rejected wrong-initial-machine])
(test.equal incomplete-witness
  (program-test.check-evidence (program-test.with-trace
    (program-test.drop-last (program-test.trace (program-test.evidence (program-test.run))))))
  [rejected incomplete-evaluation])
(test.equal extra-after-terminal
  (program-test.check-evidence (program-test.with-trace
    (append (program-test.trace (program-test.evidence (program-test.run))) [[machine [return good] []]])))
  [rejected steps-after-termination])
(test.equal malformed-trace-tail
  (program-test.check-evidence (program-test.with-trace [[machine [call r03.entry []] []] | garbage]))
  [rejected malformed-evaluation-trace])
(test.equal wrong-recorded-outcome
  (vor.check-evaluation (program-test.p) r03.entry [] [value forged]
    [vor-evaluation 0 (program-test.p) r03.entry [] [value forged]
      (program-test.trace (program-test.evidence (program-test.run)))] 100)
  [rejected wrong-evaluation-outcome])
(test.equal execution-witness-fuel
  (vor.check-evaluation (program-test.p) r03.entry [] [value good]
    (program-test.evidence (program-test.run)) 0) [unknown evaluation-fuel])
(test.equal typed-execution
  (vor.execution-typecheck (program-test.p) r03.entry [] [value good]
    (program-test.evidence (program-test.run)) 100) [accepted typed-evaluation])
(test.equal typed-execution-uncertainty
  (vor.execution-typecheck (program-test.p) r03.entry [] [value good]
    (program-test.evidence (program-test.run)) 0) [unknown evaluation-fuel])
(test.equal typed-execution-injection
  (vor.execution-typecheck (program-test.p) r03.entry [] [value good] [simple-error "no"] 100)
  [rejected evaluation-identity-mismatch])
(define program-test.claim
  -> [vor-claim 0 (test.root) [program (program-test.p)] [] [[runtime trusted-image]]
      admitted-shen-0 [evaluates r03.entry [] [value good]] concrete-derivation])
(define program-test.envelope
  -> [vor-evidence 0 (program-test.claim) (program-test.evidence (program-test.run))])
(test.equal execution-claim-valid (vor.claim? (program-test.claim)) true)
(test.equal execution-claim
  (vor.check-claim (test.root) (program-test.claim) (program-test.envelope) 100)
  [checked (program-test.claim) [accepted evaluation]])
(test.equal typed-execution-claim
  (vor.typecheck-claim (test.root) (program-test.claim) (program-test.envelope))
  [checked (program-test.claim) [accepted typed-evidence]])
(test.equal wire-execution-claim
  (vor.check-artifact (test.root) (program-test.claim) (test.ok (test.pack (program-test.envelope))) 10000 64 10000 100)
  [checked (program-test.claim) [accepted evaluation]])
(define program-test.normalization-claim
  -> [vor-claim 0 (test.root) [source (program-test.source good)] [] []
      admitted-shen-0 [normalizes (program-test.p)] concrete-derivation])
(test.equal normalization-claim
  (vor.check-claim (test.root) (program-test.normalization-claim)
    [vor-evidence 0 (program-test.normalization-claim)
      [vor-normalization 0 (program-test.source good) (program-test.p)]] 100)
  [checked (program-test.normalization-claim) [accepted normalization]])

(define program-test.variable-program
  -> (program-test.program [shen-source 0 [[define r03.identity (intern "X") -> (intern "X")]]]))
(test.equal typed-variable-source
  (vor.execution-typecheck (program-test.variable-program) r03.identity [42] [value 42]
    (program-test.evidence (vor.run (program-test.variable-program) r03.identity [42] 100)) 100)
  [accepted typed-evaluation])
(test.equal kernel-name-is-not-an-admitted-definition
  (vor.normalize [shen-source 0 [[define vor.normalize (intern "X") -> false]]])
  [rejected reserved-or-invalid-function])
(test.equal primitive-name-is-not-an-admitted-definition
  (vor.normalize [shen-source 0 [[define + -> false]]]) [rejected reserved-or-invalid-function])
(test.equal native-normalizer-still-intact (hd (vor.normalize (program-test.source good))) ok)
(test.equal closure-argument-rejected
  (vor.run (program-test.p) r03.entry [(function vor.normalize)] 100) [rejected invalid-program-or-call])
(test.equal runtime-argument-arity
  (vor.run (program-test.p) r03.entry [0] 100) [rejected invalid-program-or-call])
(test.equal foreign-program-in-witness
  (vor.check-evaluation (program-test.program (program-test.source other)) r03.entry [] [value good]
    (program-test.evidence (program-test.run)) 100) [rejected evaluation-identity-mismatch])
(test.equal foreign-args-in-witness
  (vor.check-evaluation (program-test.variable-program) r03.identity [43] [value 42]
    (program-test.evidence (vor.run (program-test.variable-program) r03.identity [42] 100)) 100)
  [rejected evaluation-identity-mismatch])
(define program-test.changing-claim
  -> [vor-claim 0 (test.root) [program (program-test.variable-program)] [] []
      admitted-shen-0 [evaluates r03.identity [43] [value 43]] concrete-derivation])
(test.equal unrelated-execution-claim
  (vor.check-claim (test.root) (program-test.changing-claim) (program-test.envelope) 100)
  [rejected claim-mismatch])


(program-test.check repeated-inside-pattern (program-test.clauses) r03.diagonal [[a | a]] [value matched])
(program-test.check repeated-inside-pattern-mismatch (program-test.clauses) r03.diagonal [[a a]] [value different])
(program-test.check forward-mutual-recursion (program-test.clauses) r03.even [[a b c]] [value false])
(test.equal diverging-guard-is-not-false
  (vor.run (program-test.program (program-test.clauses)) r03.guard-loop [anything] 100)
  [unknown evaluation-fuel])


(program-test.check mismatched-pattern-does-not-run-guard
  (program-test.clauses) r03.skip-guard [anything] [value fallback])
(program-test.closed returned-error-is-data [cons error [cons bad []]] [value [error bad]])
(define program-test.with-entry
  Body -> (let S (program-test.clauses)
    [shen-source 0 [[define r03.entry -> Body] | (hd (tl (tl S)))]]))
(program-test.check ignored-user-argument-is-strict
  (program-test.with-entry [r03.first [hd []]]) r03.entry [] [error [primitive-domain hd]])
