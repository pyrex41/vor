\\ Untrusted constructor of explicit syntax-directed expression derivations.
\\ It supplies no acceptance flag; kernel/admit.shen checks the result.
(tc -)
(define vor.construct-expression
  [local _] -> [local]
  [literal C] -> [constructor C []]
  [primitive cons [[literal C] Tail]] ->
    [constructor C (vor.construct-expression-list (vor.admit-expression-list Tail))]
  [invoke Name Es] -> [call Name (map (function vor.construct-expression) Es)]
  [bind Val Body] -> [let (vor.construct-expression Val) (vor.construct-expression Body)]
  _ -> [unsupported])
(define vor.construct-expression-list
  [expressions Es] -> (map (function vor.construct-expression) Es)
  _ -> [[unsupported]])
(define vor.construct-definition
  Sig [contract Name Args _ M _] P ->
    (vor.construct-definition-data Name
      (vor.algebra-data (vor.admit-at Args M) Sig)
      (vor.program-function Name (vor.program-definitions P))))
(define vor.construct-definition-data
  Name [constructors Cs] [function Name _ Clauses] ->
    [definition Name (vor.construct-cases Cs Clauses)]
  Name _ _ -> [definition Name []])
(define vor.construct-cases
  [] [] -> []
  [[C _] | Cs] [[clause _ _ Body] | Bs] ->
    [[case C (vor.construct-expression Body)] | (vor.construct-cases Cs Bs)]
  _ _ -> [[unsupported]])
(define vor.construct
  P Sig Cs -> (map (/. C (vor.construct-definition Sig C P)) Cs))
