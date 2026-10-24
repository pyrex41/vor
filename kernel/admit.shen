\\ R05 trusted construction checking and source-bound admission. This is a
\\ deliberately restricted total subset of R03, not a test-based totality gate.
(tc -)

\\ The expected pattern is the representation of an algebraic constructor;
\\ only its field variables and non-measure arguments may bind source slots.
(define vor.admit-shape
  Sig [v I] Sort -> [shape-var [v I] Sort]
  Sig [app C []] _ -> [shape-atom C]
  Sig [app C Ts] _ -> [shape-cons [shape-atom C]
    (vor.admit-shapes Sig Ts (vor.admit-constructor-fields C Sig))])
(define vor.admit-constructor-fields
  C Sig -> (vor.admit-fields-of (vor.algebra-constructor C Sig)))
(define vor.admit-fields-of [function Fields _] -> Fields)
(define vor.admit-shapes
  _ [] [] -> [shape-atom []]
  Sig [T | Ts] [S | Ss] -> [shape-cons (vor.admit-shape Sig T S) (vor.admit-shapes Sig Ts Ss)])
(define vor.admit-pattern
  [pvar I] [shape-var T S] Env ->
    (if (= I (length Env)) [bindings (append Env [[T S]])] [rejected nonlinear-pattern])
  [literal V] [shape-atom V] Env -> [bindings Env]
  [pcons H T] [shape-cons A B] Env -> (vor.admit-pattern-tail T B (vor.admit-pattern H A Env))
  _ _ _ -> [rejected total-pattern])
(define vor.admit-pattern-tail
  T B [bindings Env] -> (vor.admit-pattern T B Env)
  _ _ R -> R)
(define vor.admit-patterns
  _ [] [] [] Env -> [bindings Env]
  Sig [P | Ps] [T | Ts] [S | Ss] Env ->
    (vor.admit-patterns-next Sig Ps Ts Ss (vor.admit-pattern P (vor.admit-shape Sig T S) Env))
  _ _ _ _ _ -> [rejected total-pattern-arity])
(define vor.admit-patterns-next
  Sig Ps Ts Ss [bindings Env] -> (vor.admit-patterns Sig Ps Ts Ss Env)
  _ _ _ _ R -> R)

(define vor.replace-at
  [_ | Xs] 0 T -> [T | Xs]
  [X | Xs] I T -> [X | (vor.replace-at Xs (- I 1) T)])
(define vor.without-at
  [_ | Xs] 0 -> Xs
  [X | Xs] I -> [X | (vor.without-at Xs (- I 1))])
(define vor.admit-arguments
  Args M C Fields ->
    (vor.admit-arguments-at Args M C Fields (length Fields) 0))
(define vor.admit-arguments-at
  [] _ _ _ _ _ -> []
  [_ | As] M C Fields N I ->
    [[app C (vor.algebra-variables N 0)] |
      (vor.admit-arguments-at As M C Fields N (+ I 1))] where (= I M)
  [_ | As] M C Fields N I ->
    [[v (+ N (if (< I M) I (- I 1)))] |
      (vor.admit-arguments-at As M C Fields N (+ I 1))])
(define vor.admit-smaller
  [] _ _ -> []
  [S | Ss] S I -> [[v I] | (vor.admit-smaller Ss S (+ I 1))]
  [_ | Ss] S I -> (vor.admit-smaller Ss S (+ I 1)))

\\ R03 constructor expressions are cons trees with a fixed tag and exact list
\\ spine. No primitive invocation is replaced by a symbolic user callback.
(define vor.admit-expression-list
  [literal []] -> [expressions []]
  [primitive cons [H T]] -> (vor.admit-expression-cons H (vor.admit-expression-list T))
  _ -> invalid)
(define vor.admit-expression-cons
  H [expressions Ts] -> [expressions [H | Ts]]
  _ _ -> invalid)
(define vor.admit-expr
  Sig V Env Context [local I] [local] -> (vor.admit-local (vor.fol-at Env I))
  Sig V Env Context [literal C] [constructor C []] ->
    (vor.admit-ctor Sig V Env Context C [] [] (vor.algebra-constructor C Sig))
  Sig V Env Context [primitive cons [[literal C] Tail]] [constructor C Proofs] ->
    (vor.admit-ctor-list Sig V Env Context C Proofs (vor.admit-expression-list Tail))
  Sig V Env Context [invoke Name Es] [call Name Proofs] ->
    (vor.admit-call Sig Context Name (vor.admit-exprs Sig V Env Context Es Proofs))
  Sig V Env Context [bind Val Body] [let A B] ->
    (vor.admit-let Sig V Env Context Body B (vor.admit-expr Sig V Env Context Val A))
  _ _ _ _ _ _ -> [rejected construction-rule])
(define vor.admit-local
  [found [T S]] -> [typed T S]
  _ -> [rejected construction-local])
(define vor.admit-ctor-list
  Sig V Env Context C Ps [expressions Es] ->
    (vor.admit-ctor Sig V Env Context C Es Ps (vor.algebra-constructor C Sig))
  _ _ _ _ _ _ _ -> [rejected constructor-representation])
(define vor.admit-ctor
  Sig V Env Context C Es Ps [function Fields S] ->
    (vor.admit-ctor-typed C Fields S (vor.admit-exprs Sig V Env Context Es Ps))
  _ _ _ _ _ _ _ _ -> [rejected construction-constructor])
(define vor.admit-exprs
  _ _ _ _ [] [] -> [typed-arguments [] []]
  Sig V Env Context [E | Es] [P | Ps] ->
    (vor.admit-exprs-next (vor.admit-expr Sig V Env Context E P)
      (vor.admit-exprs Sig V Env Context Es Ps))
  _ _ _ _ _ _ -> [rejected construction-arity])
(define vor.admit-exprs-next
  [typed T S] [typed-arguments Ts Ss] -> [typed-arguments [T | Ts] [S | Ss]]
  [rejected Why] _ -> [rejected Why]
  _ R -> R)
(define vor.admit-ctor-typed
  C Fields S [typed-arguments Ts Fields] -> [typed [app C Ts] S]
  _ _ _ [rejected Why] -> [rejected Why]
  _ _ _ _ -> [rejected constructor-field-sort])
(define vor.admit-let
  Sig V Env Context Body Proof [typed T S] ->
    (vor.admit-expr Sig V [[T S] | Env] Context Body Proof)
  _ _ _ _ _ _ R -> R)
(define vor.admit-call
  Sig [construction Name Args M Actual Smaller Earlier] Name [typed-arguments Ts Args] ->
    (if (and (vor.member? (vor.admit-at Ts M) Smaller)
             (= (vor.without-at Ts M) (vor.without-at Actual M)))
      (vor.admit-call-result Name Ts (vor.fol-function Name (vor.fol-functions Sig)))
      [rejected nondecreasing-or-changed-parameters])
  Sig [construction _ _ _ _ _ Earlier] Name [typed-arguments Ts Ss] ->
    (if (vor.member? [Name Ss (vor.admit-function-result Name Sig)] Earlier)
      (vor.admit-call-result Name Ts (vor.fol-function Name (vor.fol-functions Sig)))
      [rejected unadmitted-call])
  _ _ _ R -> R)
(define vor.admit-at
  Xs I -> (vor.admit-found (vor.fol-at Xs I)))
(define vor.admit-found [found X] -> X)
(define vor.admit-function-result
  Name Sig -> (vor.admit-result (vor.fol-function Name (vor.fol-functions Sig))))
(define vor.admit-result [function _ S] -> S)
(define vor.admit-call-result
  Name Ts [function _ S] -> [typed [app Name Ts] S])

(define vor.construct-check
  P Sig Cs Proof ->
    (trap-error
      (if (vor.admission-domain? P Sig Cs)
        (vor.construct-definitions P Sig Cs Proof [])
        [rejected admission-domain])
      (/. E [unknown construction-checker-error])))
(define vor.construct-definitions
  _ _ [] [] _ -> [constructed []]
  P Sig [[contract Name Args Result M Post] | Cs]
    [[definition Name Branches] | Ds] Earlier ->
    (vor.construct-definitions-next
      (vor.construct-function Sig Name Args Result M Branches Earlier
        (vor.program-function Name (vor.program-definitions P)))
      (vor.construct-definitions P Sig Cs Ds (append Earlier [[Name Args Result]])))
  _ _ _ _ _ -> [rejected construction-definitions])
(define vor.construct-definitions-next
  [constructed Equations] [constructed Rest] -> [constructed (append Equations Rest)]
  [rejected Why] _ -> [rejected Why]
  [unknown Why] _ -> [unknown Why]
  _ R -> R)
(define vor.construct-function
  Sig Name Args Result M Branches Earlier [function Name Arity Clauses] ->
    (if (= Arity (length Args))
      (vor.construct-function-data Sig Name Args Result M Branches Earlier Clauses
        (vor.algebra-data (vor.admit-at Args M) Sig))
      [rejected construction-function-arity])
  _ _ _ _ _ _ _ _ -> [rejected construction-function])
(define vor.construct-function-data
  Sig Name Args Result M Bs Earlier Clauses [constructors Cs] ->
    (vor.construct-branches Sig Name Args Result M Earlier Cs Clauses Bs)
  _ _ _ _ _ _ _ _ _ -> [rejected construction-measure-sort])
(define vor.construct-branches
  _ _ _ _ _ _ [] [] [] -> [constructed []]
  Sig Name Args Result M Earlier [[C Fields] | Cs]
    [[clause Patterns [literal true] Body] | Clauses] [[case C Proof] | Bs] ->
    (let Actual (vor.admit-arguments Args M C Fields)
      V (append Fields (vor.without-at Args M))
      (vor.construct-definitions-next
        (vor.construct-branch Sig V Name Result Body Proof Actual
          [construction Name Args M Actual
            (vor.admit-smaller Fields (vor.admit-at Args M) 0) Earlier]
          (vor.admit-patterns Sig Patterns Actual Args []))
        (vor.construct-branches Sig Name Args Result M Earlier Cs Clauses Bs)))
  _ _ _ _ _ _ _ _ _ -> [rejected construction-coverage-or-guard])
(define vor.construct-branch
  Sig V Name Result Body Proof Actual Context [bindings Env] ->
    (vor.construct-branch-result V Name Result Actual (vor.admit-expr Sig V Env Context Body Proof))
  _ _ _ _ _ _ _ _ R -> R)
(define vor.construct-branch-result
  V Name Result Actual [typed T Result] ->
    [constructed [(vor.quantify V [equal Result [app Name Actual] T])]]
  _ _ _ _ [typed _ _] -> [rejected construction-result-sort]
  _ _ _ _ R -> R)

(define vor.admit
  P Sig Cs [vor-admission 0 P Sig Cs Construction Posts] Fuel ->
    (trap-error
      (if (and (vor.nat? Fuel) (<= Fuel 65535))
        (vor.admit-constructed Sig Cs Posts Fuel (vor.construct-check P Sig Cs Construction))
        [rejected invalid-proof-fuel])
      (/. E [unknown admission-checker-error]))
  _ _ _ _ _ -> [rejected admission-identity])
(define vor.admit-constructed
  Sig Cs Posts Fuel [constructed Equations] ->
    (vor.admit-post-finish (vor.admit-posts Sig Cs Posts Equations Fuel))
  _ _ _ _ R -> R)
(define vor.admit-posts
  _ [] [] _ Fuel -> [proved Fuel]
  Sig [[contract Name Args Result M Post] | Cs] [[post Name E] | Ps] Equations Fuel ->
    (vor.admit-post-next Sig Cs Ps Equations
      (vor.fol-derive Sig [] Equations (vor.contract-theorem [contract Name Args Result M Post]) E Fuel))
  _ _ _ _ _ -> [rejected contract-proof-coverage])
(define vor.admit-post-next
  Sig Cs Ps Equations [proved Fuel] -> (vor.admit-posts Sig Cs Ps Equations Fuel)
  _ _ _ _ R -> R)
(define vor.admit-post-finish
  [proved _] -> [accepted total-admission]
  R -> R)

(define vor.admission-code?
  P Sig Cs Code -> (vor.admission-decoded? P Sig Cs (vor.decode-claim-literal Code)))
(define vor.admission-decoded?
  P Sig Cs [ok E] -> (= (vor.admit P Sig Cs E 65535) [accepted total-admission])
  _ _ _ _ -> false)
(datatype vor-total-admission
  if (vor.admission-domain? P Sig Cs)
  if (vor.admission-code? P Sig Cs E)
  ______________________________________________________
  E : (vor-admits P Sig Cs);)
(define vor.admission-typecheck
  P Sig Cs E Fuel ->
    (trap-error (vor.admission-type-result P Sig Cs E (vor.admit P Sig Cs E Fuel))
      (/. Error [unknown admission-typechecker-error])))
(define vor.admission-type-result
  P Sig Cs E [accepted total-admission] ->
    (if (vor.system-s? E [vor-admits P Sig Cs]) [accepted typed-admission] [rejected admission-type])
  _ _ _ _ R -> R)

\\ Expose the exact definition equations only after their total construction
\\ derivation checks. The theorem is closed and has no caller-added axioms.
(define vor.check-constructed-theorem
  P Sig Cs Construction Theorem Evidence Fuel ->
    (trap-error
      (vor.constructed-theorem-result Sig Theorem Evidence Fuel
        (vor.construct-check P Sig Cs Construction))
      (/. E [unknown constructed-theorem-error])))
(define vor.constructed-theorem-result
  Sig Theorem Evidence Fuel [constructed Equations] ->
    (vor.constructed-theorem-finish (vor.fol-check Sig [] Equations Theorem Evidence Fuel))
  _ _ _ _ R -> R)
(define vor.constructed-theorem-finish
  [accepted first-order-derivation] -> [accepted constructed-theorem]
  R -> R)

(define vor.run-admitted
  P Sig Cs Evidence Name Args ProofFuel RunFuel ->
    (vor.run-admitted-checked P Sig Cs Name Args RunFuel (vor.admit P Sig Cs Evidence ProofFuel)))
(define vor.run-admitted-checked
  P Sig Cs Name Args Fuel [accepted total-admission] ->
    (vor.run-admitted-contract P Sig Name Args Fuel (vor.contract-find Name Cs))
  _ _ _ _ _ _ R -> R)
(define vor.run-admitted-contract
  P Sig Name Args Fuel [contract Name Sorts Result _ _] ->
    (if (not (= (vor.algebra-value-terms Sig Sorts Args) invalid))
      (vor.run-admitted-result P Sig Name Args Result Fuel (vor.run P Name Args Fuel))
      [rejected input-outside-contract])
  _ _ _ _ _ _ -> [rejected missing-contract])
(define vor.run-admitted-result
  P Sig Name Args Result Fuel [evaluated [value V] E] ->
    (if (vor.algebra-value? Sig Result V)
      (if (= (vor.check-evaluation P Name Args [value V] E Fuel) [accepted evaluation])
        [executed-admitted [value V] E] [unknown execution-witness])
      [unknown construction-evaluation-disagreement])
  _ _ _ _ _ _ [evaluated [error R] _] -> [unknown [admitted-execution-error R]]
  _ _ _ _ _ _ R -> R)

(define vor.construction-root-inventory
  -> [vor-construction-root 1 [local constructor let call]
      [complete-ordered-constructor-coverage linear-patterns
       strict-immediate-self-field unchanged-other-arguments earlier-dependencies]
      [initial-algebra-totality exact-r03-equations checked-first-order-postconditions]])
