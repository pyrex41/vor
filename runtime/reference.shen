\\ Untrusted execution producer and a separate trace-witness acceptance walk.
\\ Both share the declared small-step relation, not a second application.
(tc -)

(define vor.run
  Program Name Args Fuel ->
    (trap-error
      (if (vor.program-call? Program Name Args)
        (if (and (vor.nat? Fuel) (<= Fuel 65535))
          (vor.run-steps Program Name Args
            [machine [call Name Args] []] Fuel [[machine [call Name Args] []]])
          [rejected invalid-evaluation-fuel])
        [rejected invalid-program-or-call])
      (/. E [unknown evaluator-error])))
(define vor.run-steps
  P Name Args State Fuel Acc ->
    (vor.run-outcome P Name Args State Fuel Acc (vor.machine-outcome State)))
(define vor.run-outcome
  P Name Args _ _ Acc [finished Outcome] ->
    [evaluated Outcome [vor-evaluation 0 P Name Args Outcome (reverse Acc)]]
  _ _ _ _ 0 _ running -> [unknown evaluation-fuel]
  P Name Args State Fuel Acc running ->
    (let Next (vor.machine-step P State)
      (vor.run-steps P Name Args Next (- Fuel 1) [Next | Acc])))

(define vor.check-evaluation
  P Name Args Outcome Evidence Fuel ->
    (trap-error
      (if (vor.program-call? P Name Args)
        (if (and (vor.nat? Fuel) (<= Fuel 65535))
          (vor.check-evaluation-envelope P Name Args Outcome Evidence Fuel)
          [rejected invalid-evaluation-fuel])
        [rejected invalid-program-or-call])
      (/. E [unknown evaluation-checker-error])))
(define vor.check-evaluation-envelope
  P Name Args Outcome [vor-evaluation 0 P Name Args Outcome [Start | States]] Fuel ->
    (if (= Start [machine [call Name Args] []])
      (vor.check-evaluation-steps P Outcome Start States Fuel)
      [rejected wrong-initial-machine])
  _ _ _ _ _ _ -> [rejected evaluation-identity-mismatch])
(define vor.check-evaluation-steps
  P Outcome Current States Fuel ->
    (vor.check-evaluation-outcome P Outcome Current States Fuel (vor.machine-outcome Current)))
(define vor.check-evaluation-outcome
  _ Outcome _ [] _ [finished Outcome] -> [accepted evaluation]
  _ _ _ [] _ [finished _] -> [rejected wrong-evaluation-outcome]
  _ _ _ [_ | _] _ [finished _] -> [rejected steps-after-termination]
  _ _ _ [] _ running -> [rejected incomplete-evaluation]
  _ _ _ _ 0 running -> [unknown evaluation-fuel]
  P Outcome Current [Next | Rest] Fuel running ->
    (if (= Next (vor.machine-step P Current))
      (vor.check-evaluation-steps P Outcome Next Rest (- Fuel 1))
      [rejected illegal-evaluation-step])
  _ _ _ _ _ _ -> [rejected malformed-evaluation-trace])

(define vor.evaluation-code?
  P Name Args Outcome Code ->
    (vor.evaluation-decoded? P Name Args Outcome (vor.decode-claim-literal Code)))
(define vor.evaluation-decoded?
  P Name Args Outcome [ok Evidence] ->
    (= (vor.check-evaluation P Name Args Outcome Evidence 65535) [accepted evaluation])
  _ _ _ _ _ -> false)
(datatype vor-execution
  if (vor.program-call? P Name Args)
  if (vor.evaluation-code? P Name Args Outcome E)
  ______________________________________________________
  E : (vor-evaluates P Name Args Outcome);)

(define vor.program-outcome?
  [value V] -> (vor.program-value? V)
  [error nonboolean-condition] -> true
  [error nonboolean-guard] -> true
  [error invalid-local] -> true
  [error [primitive-domain Name]] -> (not (= (vor.primitive-arity Name) missing))
  [error [no-clause Name]] -> (vor.source-name? Name)
  [error [call-arity Name]] -> (vor.source-name? Name)
  [error [unknown-function Name]] -> (vor.source-name? Name)
  _ -> false)
(define vor.execution-typecheck
  P Name Args Outcome Evidence Fuel ->
    (trap-error
      (vor.execution-typecheck-result P Name Args Outcome Evidence
        (vor.check-evaluation P Name Args Outcome Evidence Fuel))
      (/. E [unknown execution-typechecker-error])))
(define vor.execution-typecheck-result
  P Name Args Outcome Evidence [accepted evaluation] ->
    (if (vor.system-s? Evidence [vor-evaluates P Name Args Outcome])
      [accepted typed-evaluation] [rejected invalid-execution-evidence])
  _ _ _ _ _ R -> R)
