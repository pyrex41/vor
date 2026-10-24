\\ The expected claim/root come from the verifier's trusted configuration.
\\ Nothing in an artifact authorizes its own root or its own expected claim.
(tc -)

(define vor.check-claim
  Root Expected Artifact Depth ->
    (if (vor.root? Root)
      (if (vor.claim? Expected)
        (if (= Root (vor.claim-root Expected))
          (if (vor.nat? Depth)
            (trap-error (vor.check-bound Expected Artifact Depth)
              (/. E [unknown checker-error]))
            [rejected invalid-budget])
          [rejected root-mismatch])
        [rejected malformed-claim])
      [rejected malformed-root]))

(define vor.check-bound
  Expected [vor-evidence 0 Actual Evidence] Depth ->
    (if (= Expected Actual)
      (vor.claim-result Expected (vor.claim-dispatch Expected Evidence Depth))
      [rejected claim-mismatch])
  _ _ _ -> [rejected malformed-artifact])

(define vor.claim-dispatch
  [vor-claim 0 _ [model M] _ _ boolean-states [invariant] finite-proof] E _ ->
    (vor.check-certificate M E)
  [vor-claim 0 _ [model M] _ _ boolean-states [trace-prefix T] trace-check] E _ ->
    (if (= T E) (vor.trace M E) [rejected trace-mismatch])
  [vor-claim 0 _ logic _ _ intuitionistic-propositions [derives G P] concrete-derivation] E D ->
    (vor.proof G P E D)
  [vor-claim 0 _ [first-order Sig Vars] _ _ constructive-first-order [derives G P] concrete-derivation] E Fuel ->
    (vor.fol-check Sig Vars G P E Fuel)
  [vor-claim 0 _ [program P] _ _ admitted-shen-0 [evaluates Name Args Outcome] concrete-derivation] E Fuel ->
    (vor.check-evaluation P Name Args Outcome E Fuel)
  [vor-claim 0 _ [source Source] _ _ admitted-shen-0 [normalizes P] concrete-derivation] E _ ->
    (vor.check-normalization Source E)
  [vor-claim 0 _ [program P] _ _ constructor-stack-0 [compiles Artifact] concrete-derivation] E _ ->
    (if (= E Artifact) (vor.check-compilation P Artifact) [rejected compilation-evidence-mismatch])
  [vor-claim 0 _ [total-program P Sig Cs] _ _ total-shen-1 [total-contracts] generic-proof] E Fuel ->
    (vor.admit P Sig Cs E Fuel)
  [vor-claim 0 _ [total-program P Sig Cs] _ _ total-shen-1 [theorem T] generic-proof]
    [constructed-theorem 0 Construction Proof] Fuel ->
    (vor.check-constructed-theorem P Sig Cs Construction T Proof Fuel)
  _ _ _ -> [rejected unsupported-claim-evidence])

\\ Preserve the ENTIRE expected claim on success; not a reusable safe flag.
\\ A supplied accepted record is never routed around the semantic checkers.
(define vor.claim-result
  C [accepted finite-invariant N] -> [checked C [accepted finite-invariant N]]
  C [accepted trace-prefix N] -> [checked C [accepted trace-prefix N]]
  C [accepted derivation] -> [checked C [accepted derivation]]
  C [accepted first-order-derivation] -> [checked C [accepted first-order-derivation]]
  C [accepted evaluation] -> [checked C [accepted evaluation]]
  C [accepted normalization] -> [checked C [accepted normalization]]
  C [accepted compilation] -> [checked C [accepted compilation]]
  C [accepted total-admission] -> [checked C [accepted total-admission]]
  C [accepted constructed-theorem] -> [checked C [accepted constructed-theorem]]
  _ R -> R)

\\ System S receives literal cons syntax. Decode only the closed data grammar;
\\ never execute the supplied term to obtain evidence.
(define vor.decode-claim-literal
  [cons H T] -> (vor.decode-cons (vor.decode-claim-literal H) (vor.decode-claim-literal T))
  X -> [ok X] where (and (not (cons? X)) (vor.data? X))
  _ -> [rejected nonliteral])

(define vor.typed-claim-code?
  Code Root C -> (vor.typed-claim-decoded (vor.decode-claim-literal Code) Root C))

(define vor.typed-claim-decoded
  [ok Artifact] Root C ->
    (vor.checked-for? C (vor.check-claim Root C Artifact 1000))
  _ _ _ -> false)

(define vor.checked-for?
  C [checked C _] -> true
  _ _ -> false)

(datatype vor-bound-claims
  if (vor.root? Root)
  if (vor.claim? C)
  if (= Root (vor.claim-root C))
  if (vor.typed-claim-code? E Root C)
  ______________________________________________________
  E : (vor-bound-evidence Root C);)

(define vor.typecheck-claim
  Root C Artifact ->
    (if (and (vor.root? Root) (vor.claim? C))
      (if (= Root (vor.claim-root C))
        (trap-error
          (vor.typecheck-claim-result Root C Artifact (vor.check-claim Root C Artifact 1000))
          (/. E [unknown typechecker-error]))
        [rejected root-mismatch])
      [rejected malformed-claim]))


(define vor.typecheck-claim-result
  Root C Artifact [checked C _] ->
    (if (vor.system-s? Artifact [vor-bound-evidence Root C])
      [checked C [accepted typed-evidence]] [rejected invalid-evidence])
  _ _ _ [unknown Reason] -> [unknown Reason]
  _ _ _ _ -> [rejected invalid-evidence])
