\\ R05 total contracts: all inputs of the declared algebraic sorts; no implicit
\\ precondition. Post is scoped by [Result | Inputs], nearest first.
(tc -)
(define vor.contract-functions
  [] -> []
  [[contract Name Args Result _ _] | Cs] -> [[Name Args Result] | (vor.contract-functions Cs)]
  _ -> [[invalid]])
(define vor.contract-find
  Name [[contract Name Args Result Measure Post] | _] -> [contract Name Args Result Measure Post]
  Name [_ | Cs] -> (vor.contract-find Name Cs)
  _ [] -> missing)
(define vor.contract-data-sorts?
  _ [] -> true
  Sig [S | Ss] -> (and (not (= (vor.algebra-data S Sig) missing)) (vor.contract-data-sorts? Sig Ss))
  _ _ -> false)
(define vor.contracts?
  Sig Cs ->
    (and (vor.fol-signature? Sig)
      (and (vor.contract-signature? Sig Cs)
        (and (not (= Cs [])) (vor.contract-list? Sig Cs)))))
(define vor.contract-signature?
  [fol-signature 1 [] Fs [] Data] Cs ->
    (and (= Fs (vor.contract-functions Cs))
         (vor.contract-algebras? (vor.algebra-sort-names Data) Data))
  _ _ -> false)
(define vor.contract-list?
  _ [] -> true
  Sig [[contract Name Args Result Measure Post] | Cs] ->
    (and (vor.source-name? Name)
      (and (vor.contract-data-sorts? Sig [Result | Args])
        (and (vor.nat? Measure)
          (and (not (= (vor.fol-at Args Measure) missing))
            (and (vor.fol-formula? Sig [Result | Args] Post) (vor.contract-list? Sig Cs))))))
  _ _ -> false)
(define vor.quantify
  Sorts P -> (vor.quantify-forward (reverse Sorts) P))
(define vor.quantify-forward
  [] P -> P
  [S | Ss] P -> [forall S (vor.quantify-forward Ss P)])
(define vor.contract-theorem
  [contract Name Args Result _ Post] ->
    (vor.quantify Args (vor.fol-sub Post [app Name (vor.algebra-variables (length Args) 0)] 0)))
(define vor.admission-domain?
  P Sig Cs ->
    (and (vor.program? P)
      (and (vor.contracts? Sig Cs)
        (= (vor.header-names (vor.source-headers-list P))
           (map (function hd) (vor.contract-functions Cs))))))
(define vor.source-headers-list
  P -> (vor.definition-headers (vor.program-definitions P)))
(define vor.definition-headers
  [] -> []
  [[function Name Arity _] | Ds] -> [[signature Name Arity] | (vor.definition-headers Ds)])

\\ Admission needs a complete value encoding, unlike abstract first-order
\\ signatures. Reserved tree/opaque fields await their encoding correspondence.
(define vor.contract-algebras?
  _ [] -> true
  Sorts [[data _ Constructors] | Ds] ->
    (and (vor.algebra-fields? Sorts Constructors) (vor.contract-algebras? Sorts Ds)))
