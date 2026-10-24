\\ R01: closed claims over IMPLEMENTED semantic domains, not program admission.
(tc -)

\\ In-memory metadata is inert finite tree data. Wire ingestion additionally
\\ bounds bytes/depth/nodes. Dependency order is significant for exact identity.
(define vor.data?
  [] -> true
  true -> true
  false -> true
  [H | T] -> (and (vor.data? H) (and (vor.proper? T) (vor.data? T)))
  X -> true where (symbol? X)
  X -> true where (string? X)
  X -> (vor.nat? X) where (number? X)
  _ -> false)

(define vor.bindings?
  [] -> true
  [[Name Value] | Rest] ->
    (and (vor.names? [Name])
      (and (vor.data? Value)
        (and (not (vor.member? Name (vor.keys Rest))) (vor.bindings? Rest))))
  _ -> false)

(define vor.root?
  [vor-root 0 Rules Host] ->
    (and (string? Rules) (and (not (= Rules ""))
      (and (string? Host) (not (= Host "")))))
  _ -> false)

(define vor.claim?
  [vor-claim 0 Root Subject Dependencies Assumptions Domain Judgment Kind] ->
    (and (vor.root? Root)
      (and (vor.bindings-safe? Dependencies)
        (and (vor.bindings-safe? Assumptions)
             (vor.claim-domain? Subject Domain Judgment Kind))))
  _ -> false)

\\ Validate pair shape before keys; malformed metadata is rejection, not a host error.
(define vor.binding-shape?
  [] -> true
  [[_ _] | Rest] -> (vor.binding-shape? Rest)
  _ -> false)

(define vor.bindings-safe?
  X -> (and (vor.binding-shape? X) (vor.bindings? X)))

(define vor.claim-domain?
  [model M] boolean-states [invariant] finite-proof -> (vor.model? M)
  [model M] boolean-states [trace-prefix T] trace-check ->
    (and (vor.model? M) (vor.data? T))
  logic intuitionistic-propositions [derives G P] concrete-derivation ->
    (and (vor.context? G) (vor.formula? P))
  [first-order Sig Vars] constructive-first-order [derives G P] concrete-derivation ->
    (vor.fol-sequent? Sig Vars G P)
  [program P] admitted-shen-0 [evaluates Name Args Outcome] concrete-derivation ->
    (and (vor.program-call? P Name Args) (vor.program-outcome? Outcome))
  [source Source] admitted-shen-0 [normalizes P] concrete-derivation ->
    (= (vor.normalize Source) [ok P])
  [program P] constructor-stack-0 [compiles Artifact] concrete-derivation ->
    (and (vor.program? P) (vor.compiled-identity? P Artifact))
  [total-program P Sig Cs] total-shen-1 [total-contracts] generic-proof ->
    (vor.admission-domain? P Sig Cs)
  [total-program P Sig Cs] total-shen-1 [theorem Theorem] generic-proof ->
    (and (vor.admission-domain? P Sig Cs) (vor.fol-formula? Sig [] Theorem))
  _ _ _ _ -> false)

(define vor.claim-root
  [vor-claim 0 R _ _ _ _ _ _] -> R)

(define vor.claim-subject
  [vor-claim 0 _ S _ _ _ _ _] -> S)

(define vor.claim-kind
  [vor-claim 0 _ _ _ _ _ _ K] -> K)

(define vor.claim-assumptions
  [vor-claim 0 _ _ _ A _ _ _] -> A)

(define vor.claim-judgment
  [vor-claim 0 _ _ _ _ _ J _] -> J)
