\\ Untrusted compiler producer; independent syntax-directed translation check.
\\ Only the R05 pure constructor/let/call expression subset is supported.
(tc -)
(define vor.compile-expression
  [literal V] -> [[push V]]
  [local I] -> [[get I]]
  [primitive cons [A B]] -> (append (vor.compile-expression A)
    (append (vor.compile-expression B) [[join]]))
  [bind A B] -> (append (vor.compile-expression A)
    (append [[enter]] (append (vor.compile-expression B) [[leave]])))
  [invoke Name Args] -> (append (vor.compile-expressions Args) [[call Name (length Args)]])
  _ -> [[unsupported]])
(define vor.compile-expressions
  [] -> []
  [E | Es] -> (append (vor.compile-expression E) (vor.compile-expressions Es)))
(define vor.compile-functions
  [] -> []
  [[function Name Arity Clauses] | Fs] ->
    [[function Name Arity (vor.compile-clauses Clauses)] | (vor.compile-functions Fs)])
(define vor.compile-clauses
  [] -> []
  [[clause Pats Guard Body] | Cs] ->
    [[clause Pats Guard (vor.compile-expression Body)] | (vor.compile-clauses Cs)])
(define vor.compile-program
  P -> (trap-error
    (if (vor.program? P)
      [compiled [vor-compiled 0 P (vor.compile-functions (vor.program-definitions P))]]
      [rejected invalid-compilation-program])
    (/. E [unknown compiler-error])))

\\ The checker consumes a code prefix per expression and never calls compiler
\\ functions. Extra instructions, wrong arity/order, lost scope, unsupported
\\ source forms and changed source/metadata cannot pass.
(define vor.code-expect
  I [I | Rest] -> [suffix Rest]
  _ _ -> [rejected compilation-instruction])
(define vor.check-expression-code
  [literal V] Code -> (vor.code-expect [push V] Code)
  [local I] Code -> (vor.code-expect [get I] Code)
  [primitive cons [A B]] Code ->
    (vor.check-code-end [join] (vor.check-code-follow B (vor.check-expression-code A Code)))
  [bind A B] Code ->
    (vor.check-code-end [leave]
      (vor.check-code-follow B (vor.check-code-end [enter] (vor.check-expression-code A Code))))
  [invoke Name Args] Code ->
    (vor.check-code-end [call Name (length Args)] (vor.check-expressions-code Args Code))
  _ _ -> [rejected unsupported-compilation-form])
(define vor.check-code-follow
  E [suffix Code] -> (vor.check-expression-code E Code)
  _ R -> R)
(define vor.check-code-end
  I [suffix Code] -> (vor.code-expect I Code)
  _ R -> R)
(define vor.check-expressions-code
  [] Code -> [suffix Code]
  [E | Es] Code -> (vor.check-code-arguments Es (vor.check-expression-code E Code)))
(define vor.check-code-arguments
  Es [suffix Code] -> (vor.check-expressions-code Es Code)
  _ R -> R)
(define vor.check-compiled-clauses
  [] [] -> true
  [[clause Pats [literal true] Body] | Cs] [[clause Pats [literal true] Code] | Ds] ->
    (and (= (vor.check-expression-code Body Code) [suffix []]) (vor.check-compiled-clauses Cs Ds))
  _ _ -> false)
(define vor.check-compiled-functions
  [] [] -> true
  [[function Name Arity Cs] | Fs] [[function Name Arity Ds] | Gs] ->
    (and (vor.check-compiled-clauses Cs Ds) (vor.check-compiled-functions Fs Gs))
  _ _ -> false)
(define vor.check-compilation
  P [vor-compiled 0 P Fs] ->
    (trap-error
      (if (and (vor.program? P) (vor.check-compiled-functions (vor.program-definitions P) Fs))
        [accepted compilation] [rejected compilation-mismatch])
      (/. E [unknown compilation-checker-error]))
  _ _ -> [rejected compilation-identity])

\\ Concrete qualification executor. Calls use the frozen reference semantics;
\\ there is no ambient function dispatch. This is not the default authority.
(define vor.code-run
  _ [] Env Stack Frames _ -> [code-result Env Stack Frames]
  _ [_ | _] _ _ _ 0 -> [unknown code-fuel]
  P [[push V] | Code] Env Stack Frames Fuel ->
    (vor.code-run P Code Env [V | Stack] Frames (- Fuel 1))
  P [[get I] | Code] Env Stack Frames Fuel ->
    (vor.code-get P Code Env Stack Frames (- Fuel 1) (vor.fol-at Env I))
  P [[join] | Code] Env [T H | Stack] Frames Fuel ->
    (vor.code-run P Code Env [[H | T] | Stack] Frames (- Fuel 1))
  P [[enter] | Code] Env [V | Stack] Frames Fuel ->
    (vor.code-run P Code [V | Env] Stack [Env | Frames] (- Fuel 1))
  P [[leave] | Code] _ Stack [Env | Frames] Fuel ->
    (vor.code-run P Code Env Stack Frames (- Fuel 1))
  P [[call Name N] | Code] Env Stack Frames Fuel ->
    (if (and (vor.nat? N) (<= N (length Stack)))
      (vor.code-call P Code Env Frames (- Fuel 1) Name (vor.code-pop N Stack []))
      [rejected code-call-stack])
  _ _ _ _ _ _ -> [rejected malformed-code-machine])
(define vor.code-get
  P Code Env Stack Frames Fuel [found V] -> (vor.code-run P Code Env [V | Stack] Frames Fuel)
  _ _ _ _ _ _ _ -> [rejected code-local])
(define vor.code-pop
  0 Stack Args -> [arguments Args Stack]
  N [V | Stack] Args -> (vor.code-pop (- N 1) Stack [V | Args]))
(define vor.code-call
  P Code Env Frames Fuel Name [arguments Args Stack] ->
    (vor.code-call-result P Code Env Frames Fuel Name Args Stack (vor.run P Name Args Fuel)))
(define vor.code-call-result
  P Code Env Frames Fuel Name Args Stack [evaluated [value V] Evidence] ->
    (if (= (vor.check-evaluation P Name Args [value V] Evidence Fuel) [accepted evaluation])
      (vor.code-run P Code Env [V | Stack] Frames (- Fuel (vor.code-evidence-cost Evidence)))
      [unknown code-call-witness])
  _ _ _ _ _ _ _ _ R -> [unknown [code-call-outcome R]])
(define vor.code-evidence-cost
  [vor-evaluation 0 _ _ _ _ States] -> (- (length States) 1))

(define vor.compiled-outcome
  P Artifact Name Args Fuel ->
    (trap-error
      (if (and (vor.nat? Fuel) (<= Fuel 65535))
        (vor.compiled-outcome-checked P Artifact Name Args Fuel) [rejected invalid-code-fuel])
      (/. E [unknown compiled-runtime-error])))
(define vor.compiled-outcome-checked
  P [vor-compiled 0 P Fs] Name Args Fuel ->
    (if (= (vor.check-compilation P [vor-compiled 0 P Fs]) [accepted compilation])
      (vor.compiled-call P Name Args Fuel (vor.program-function Name Fs))
      [rejected invalid-compiled-artifact])
  _ _ _ _ _ -> [rejected compilation-identity])
(define vor.compiled-call
  P Name Args Fuel [function Name Arity Clauses] ->
    (if (and (vor.program-values? Args) (= (length Args) Arity))
      (vor.compiled-select P Args Fuel Clauses) [rejected compiled-call-arity])
  _ _ _ _ _ -> [rejected compiled-function])
(define vor.compiled-select
  P Args Fuel [[clause Pats [literal true] Code] | Cs] ->
    (vor.compiled-match P Args Fuel Code Cs (vor.match-patterns Pats Args []))
  _ _ _ [] -> [rejected compiled-no-clause])
(define vor.compiled-match
  P _ Fuel Code _ [match Env] -> (vor.compiled-finish Env (vor.code-run P Code Env [] [] Fuel))
  P Args Fuel _ Cs no-match -> (vor.compiled-select P Args Fuel Cs))
(define vor.compiled-finish
  Env [code-result Env [V] []] -> [compiled-value V]
  _ [unknown R] -> [unknown R]
  _ R -> [rejected [compiled-machine-result R]])

(define vor.compiled-identity?
  P [vor-compiled 0 P Fs] -> (vor.data? Fs)
  _ _ -> false)
