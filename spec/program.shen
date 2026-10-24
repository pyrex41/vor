\\ R03: one inert normalization route for a closed, first-order Shen subset.
(tc -)

(define vor.source-variable?
  N -> (let S (str N)
    (and (not (= S ""))
      (and (>= (string->n (pos S 0)) 65) (<= (string->n (pos S 0)) 90)))) where (symbol? N)
  _ -> false)
(define vor.program-value?
  true -> true
  false -> true
  [] -> true
  [H | T] -> (and (vor.program-value? H) (vor.program-value? T))
  V -> true where (or (symbol? V) (string? V))
  V -> (and (vor.nat? V) (<= V 65535)) where (number? V)
  _ -> false)
(define vor.program-values?
  [] -> true
  [V | Vs] -> (and (vor.program-value? V) (vor.program-values? Vs))
  _ -> false)
(define vor.primitive-arity
  cons -> [arity 2]
  hd -> [arity 1]
  tl -> [arity 1]
  cons? -> [arity 1]
  empty? -> [arity 1]
  number? -> [arity 1]
  string? -> [arity 1]
  symbol? -> [arity 1]
  = -> [arity 2]
  _ -> missing)
(define vor.source-prefix?
  _ "" -> true
  "" _ -> false
  Text Prefix -> (and (= (pos Text 0) (pos Prefix 0))
    (vor.source-prefix? (tlstr Text) (tlstr Prefix))))
(define vor.source-reserved?
  N -> (or (vor.source-prefix? (str N) "vor.")
    (or (vor.source-prefix? (str N) "shen.")
      (vor.member? N [+ - * / < > <= >= str cn intern n->string string->n pos tlstr
        absvector absvector? address-> <-address vector vector? get-address
        type tc datatype defprolog defcc package do cond cases compile read cd
        error-to-string get-time pr read-byte write-byte open close set value
        simple-error trap-error eval-kl]))))
(define vor.source-name?
  N -> (and (vor.names? [N])
    (and (not (vor.source-variable? N))
      (and (and (not (= N (intern "_"))) (not (vor.source-reserved? N)))
        (and (= (vor.primitive-arity N) missing)
          (not (vor.member? N [define if let protect where -> <- and or not
            lambda /. freeze thaw eval eval-kl load set value open close
            read-byte write-byte input output trap-error simple-error error])))))))

\\ Native reader-level AST: [define f Pattern ... -> Body where Guard ...].
\\ Bracket/cons syntax is represented by the reader-level [cons H T] tree.
(define vor.source-rule
  [Arrow Body Where Guard | Rest] Acc -> [raw-rule (reverse Acc) Body Guard Rest]
    where (and (= Arrow (intern "->")) (= Where where))
  [Arrow Body | Rest] Acc -> [raw-rule (reverse Acc) Body true Rest]
    where (= Arrow (intern "->"))
  [P | Rest] Acc -> (vor.source-rule Rest [P | Acc])
  _ _ -> [rejected malformed-clause])
(define vor.source-headers
  [] -> [headers []]
  [[define Name | Rules] | Rest] ->
    (if (vor.source-name? Name)
      (vor.source-header Name (vor.source-rule Rules []) (vor.source-headers Rest))
      [rejected reserved-or-invalid-function])
  _ -> [rejected malformed-definition])
(define vor.source-header
  Name [raw-rule Pats _ _ _] [headers Rest] ->
    (if (vor.member? Name (vor.header-names Rest)) [rejected duplicate-function]
      [headers [[signature Name (length Pats)] | Rest]])
  _ [rejected Why] _ -> [rejected Why]
  _ _ R -> R)
(define vor.header-names
  [] -> []
  [[signature Name _] | Rest] -> [Name | (vor.header-names Rest)])
(define vor.header-arity
  Name [[signature Name Arity] | _] -> [arity Arity]
  Name [_ | Rest] -> (vor.header-arity Name Rest)
  _ [] -> missing)
(define vor.local-index
  Name [Name | _] Index -> [index Index]
  Name [_ | Rest] Index -> (vor.local-index Name Rest (+ Index 1))
  _ [] _ -> missing)

(define vor.normalize-pattern
  P Names -> [pattern [wild] Names] where (= P (intern "_"))
  [cons H T] Names -> (vor.normalize-pattern-cons T (vor.normalize-pattern H Names))
  P Names -> (vor.normalize-pattern-var P Names (vor.local-index P Names 0)) where (vor.source-variable? P)
  P Names -> (if (and (not (cons? P)) (vor.program-value? P))
    [pattern [literal P] Names] [rejected unsupported-pattern]))
(define vor.normalize-pattern-var
  _ Names [index I] -> [pattern [pvar I] Names]
  Name Names missing -> [pattern [pvar (length Names)] (append Names [Name])])
(define vor.normalize-pattern-cons
  T [pattern H Names] -> (vor.normalize-pattern-cons-end H (vor.normalize-pattern T Names))
  _ R -> R)
(define vor.normalize-pattern-cons-end
  H [pattern T Names] -> [pattern [pcons H T] Names]
  _ R -> R)
(define vor.normalize-patterns
  [] Names -> [patterns [] Names]
  [P | Ps] Names -> (vor.normalize-patterns-next Ps (vor.normalize-pattern P Names)))
(define vor.normalize-patterns-next
  Ps [pattern P Names] -> (vor.normalize-patterns-end P (vor.normalize-patterns Ps Names))
  _ R -> R)
(define vor.normalize-patterns-end
  P [patterns Ps Names] -> [patterns [P | Ps] Names]
  _ R -> R)

(define vor.normalize-expression
  Headers Names [if A B C] ->
    (vor.normalize-if (vor.normalize-expression Headers Names A)
      (vor.normalize-expression Headers Names B) (vor.normalize-expression Headers Names C))
  Headers Names [let Name Value Body] ->
    (if (vor.source-variable? Name)
      (vor.normalize-let (vor.normalize-expression Headers Names Value)
        (vor.normalize-expression Headers [Name | Names] Body))
      [rejected invalid-let-binder])
  _ _ [protect Name] -> (if (symbol? Name) [expr [literal Name]] [rejected unsupported-protect])
  _ Names Name -> (vor.normalize-local (vor.local-index Name Names 0)) where (vor.source-variable? Name)
  _ _ Name -> [rejected wildcard-expression] where (= Name (intern "_"))
  Headers Names [Name | Args] ->
    (if (and (symbol? Name) (vor.proper? Args))
      (vor.normalize-call Name (length Args)
        (vor.primitive-arity Name) (vor.header-arity Name Headers)
        (vor.normalize-expressions Headers Names Args))
      [rejected unsupported-application])
  _ _ Value -> (if (vor.program-value? Value) [expr [literal Value]] [rejected unsupported-literal]))
(define vor.normalize-local
  [index I] -> [expr [local I]]
  _ -> [rejected unbound-variable])
(define vor.normalize-if
  [expr A] [expr B] [expr C] -> [expr [branch A B C]]
  [rejected Why] _ _ -> [rejected Why]
  _ [rejected Why] _ -> [rejected Why]
  _ _ R -> R)
(define vor.normalize-let
  [expr Value] [expr Body] -> [expr [bind Value Body]]
  [rejected Why] _ -> [rejected Why]
  _ R -> R)
(define vor.normalize-expressions
  _ _ [] -> [expressions []]
  H N [E | Es] -> (vor.normalize-expressions-end (vor.normalize-expression H N E)
                    (vor.normalize-expressions H N Es)))
(define vor.normalize-expressions-end
  [expr E] [expressions Es] -> [expressions [E | Es]]
  [rejected Why] _ -> [rejected Why]
  _ R -> R)
(define vor.normalize-call
  Name Count [arity Count] _ [expressions Es] -> [expr [primitive Name Es]]
  Name Count missing [arity Count] [expressions Es] -> [expr [invoke Name Es]]
  _ _ missing missing _ -> [rejected unknown-function-or-form]
  _ _ _ _ [rejected Why] -> [rejected Why]
  _ _ _ _ _ -> [rejected call-arity])

(define vor.normalize-clauses
  _ _ [] -> [clauses []]
  Headers Arity Tokens ->
    (vor.normalize-rule Headers Arity (vor.source-rule Tokens [])))
(define vor.normalize-rule
  Headers Arity [raw-rule Patterns Body Guard Rest] ->
    (if (= (length Patterns) Arity)
      (vor.normalize-rule-patterns Headers Arity Body Guard Rest (vor.normalize-patterns Patterns []))
      [rejected inconsistent-clause-arity])
  _ _ R -> R)
(define vor.normalize-rule-patterns
  H A Body Guard Rest [patterns Patterns Names] ->
    (vor.normalize-rule-end Patterns (vor.normalize-expression H Names Guard)
      (vor.normalize-expression H Names Body) (vor.normalize-clauses H A Rest))
  _ _ _ _ _ R -> R)
(define vor.normalize-rule-end
  Patterns [expr Guard] [expr Body] [clauses Rest] ->
    [clauses [[clause Patterns Guard Body] | Rest]]
  _ [rejected Why] _ _ -> [rejected Why]
  _ _ [rejected Why] _ -> [rejected Why]
  _ _ _ R -> R)
(define vor.normalize-definitions
  _ [] -> [definitions []]
  Headers [[define Name | Rules] | Rest] ->
    (vor.normalize-definition Name (vor.header-arity Name Headers)
      (vor.normalize-clauses Headers (vor.definition-arity (vor.header-arity Name Headers)) Rules)
      (vor.normalize-definitions Headers Rest)))
(define vor.definition-arity [arity A] -> A)
(define vor.normalize-definition
  Name [arity Arity] [clauses Clauses] [definitions Rest] ->
    [definitions [[function Name Arity Clauses] | Rest]]
  _ _ [rejected Why] _ -> [rejected Why]
  _ _ _ R -> R)

(define vor.normalize
  Source -> (trap-error (vor.normalize-source Source) (/. E [rejected malformed-source])))
(define vor.normalize-source
  [shen-source 0 Definitions] ->
    (if (and (vor.proper? Definitions) (not (= Definitions [])))
      (vor.normalize-headers [shen-source 0 Definitions] Definitions (vor.source-headers Definitions))
      [rejected empty-or-improper-source])
  _ -> [rejected unsupported-source-version])
(define vor.normalize-headers
  Source Defs [headers Headers] -> (vor.normalize-finish Source (vor.normalize-definitions Headers Defs))
  _ _ R -> R)
(define vor.normalize-finish
  Source [definitions Defs] -> [ok [vor-program 0 Source Defs]]
  _ R -> R)
(define vor.program?
  [vor-program 0 Source Definitions] -> (= (vor.normalize Source) [ok [vor-program 0 Source Definitions]])
  _ -> false)
(define vor.program-definitions [vor-program 0 _ Defs] -> Defs)
(define vor.program-function
  Name [[function Name Arity Clauses] | _] -> [function Name Arity Clauses]
  Name [_ | Rest] -> (vor.program-function Name Rest)
  _ [] -> missing)
(define vor.program-call?
  P Name Args -> (and (vor.program? P)
    (and (vor.program-values? Args)
      (vor.program-call-arity? (length Args) (vor.program-function Name (vor.program-definitions P))))))
(define vor.program-call-arity?
  A [function _ A _] -> true
  _ _ -> false)
(define vor.check-normalization
  Source [vor-normalization 0 Source Program] ->
    (if (= (vor.normalize Source) [ok Program]) [accepted normalization] [rejected normalization-mismatch])
  _ _ -> [rejected normalization-source-or-version-mismatch])
