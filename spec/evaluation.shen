\\ R03 small-step relation for canonical program definitions. Every control,
\\ continuation and outcome is inert data. No host function dispatch by name.
(tc -)

(define vor.match-pattern
  [wild] _ Env -> [match Env]
  [literal V] V Env -> [match Env]
  [literal _] _ _ -> no-match
  [pvar I] V Env ->
    (if (= I (length Env)) [match (append Env [V])]
      (if (= (vor.fol-at Env I) [found V]) [match Env] no-match))
  [pcons H T] [A | B] Env -> (vor.match-pattern-next T B (vor.match-pattern H A Env))
  _ _ _ -> no-match)
(define vor.match-pattern-next
  T B [match Env] -> (vor.match-pattern T B Env)
  _ _ _ -> no-match)
(define vor.match-patterns
  [] [] Env -> [match Env]
  [P | Ps] [A | Args] Env -> (vor.match-patterns-next Ps Args (vor.match-pattern P A Env))
  _ _ _ -> no-match)
(define vor.match-patterns-next
  Ps Args [match Env] -> (vor.match-patterns Ps Args Env)
  _ _ _ -> no-match)

(define vor.primitive
  cons [H T] -> [value [H | T]]
  hd [[H | _]] -> [value H]
  tl [[_ | T]] -> [value T]
  cons? [V] -> [value (cons? V)]
  empty? [V] -> [value (= V [])]
  number? [V] -> [value (number? V)]
  string? [V] -> [value (string? V)]
  symbol? [V] -> [value (symbol? V)]
  = [L R] -> [value (= L R)]
  Name _ -> [error [primitive-domain Name]])

(define vor.machine-outcome
  [machine [return V] []] -> [finished [value V]]
  [machine [error R] []] -> [finished [error R]]
  _ -> running)
(define vor.evaluation-next
  P State -> [next (vor.machine-step P State)])
(define vor.machine-step
  _ [machine [eval [literal V] _] K] -> [machine [return V] K]
  _ [machine [eval [local I] Env] K] -> (vor.machine-local K (vor.fol-at Env I))
  _ [machine [eval [branch A B C] Env] K] ->
    [machine [eval A Env] [[branch B C Env] | K]]
  _ [machine [eval [bind Value Body] Env] K] ->
    [machine [eval Value Env] [[bind Body Env] | K]]
  _ [machine [eval [invoke Name Exprs] Env] K] ->
    [machine [arguments [user Name] Exprs Env []] K]
  _ [machine [eval [primitive Name Exprs] Env] K] ->
    [machine [arguments [primitive Name] Exprs Env []] K]
  _ [machine [arguments [user Name] [] _ Done] K] -> [machine [call Name Done] K]
  _ [machine [arguments [primitive Name] [] _ Done] K] -> [machine [primitive Name Done] K]
  _ [machine [arguments Target [E | Es] Env Done] K] ->
    [machine [eval E Env] [[argument Target Es Env Done] | K]]
  _ [machine [return V] [[argument Target Es Env Done] | K]] ->
    [machine [arguments Target Es Env (append Done [V])] K]
  _ [machine [return V] [[bind Body Env] | K]] -> [machine [eval Body [V | Env]] K]
  _ [machine [return true] [[branch Yes _ Env] | K]] -> [machine [eval Yes Env] K]
  _ [machine [return false] [[branch _ No Env] | K]] -> [machine [eval No Env] K]
  _ [machine [return _] [[branch _ _ _] | _]] -> [machine [error nonboolean-condition] []]
  P [machine [call Name Args] K] ->
    (vor.machine-call Name Args K (vor.program-function Name (vor.program-definitions P)))
  _ [machine [choose Name [] _] _] -> [machine [error [no-clause Name]] []]
  _ [machine [choose Name [[clause Pats Guard Body] | Rest] Args] K] ->
    (vor.machine-match Name Args K Guard Body Rest (vor.match-patterns Pats Args []))
  _ [machine [return true] [[guard _ Body Env _ _] | K]] -> [machine [eval Body Env] K]
  _ [machine [return false] [[guard Name _ _ Rest Args] | K]] -> [machine [choose Name Rest Args] K]
  _ [machine [return _] [[guard _ _ _ _ _] | _]] -> [machine [error nonboolean-guard] []]
  _ [machine [primitive Name Args] K] -> (vor.machine-primitive K (vor.primitive Name Args)))
(define vor.machine-local
  K [found V] -> [machine [return V] K]
  _ _ -> [machine [error invalid-local] []])
(define vor.machine-call
  Name Args K [function Name Arity Clauses] ->
    (if (= Arity (length Args)) [machine [choose Name Clauses Args] K]
      [machine [error [call-arity Name]] []])
  Name _ _ _ -> [machine [error [unknown-function Name]] []])
(define vor.machine-match
  Name Args K Guard Body Rest [match Env] ->
    [machine [eval Guard Env] [[guard Name Body Env Rest Args] | K]]
  Name Args K _ _ Rest no-match -> [machine [choose Name Rest Args] K])
(define vor.machine-primitive
  K [value V] -> [machine [return V] K]
  _ [error R] -> [machine [error R] []])
