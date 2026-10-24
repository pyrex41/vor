\\ R02: many-sorted constructive first-order syntax with de Bruijn variables.
\\ The fixed vor.tree algebra has ONLY vor.leaf and vor.node constructors.
(tc -)

(define vor.fol-sorts
  [fol-signature 1 Sorts _ _ Data] -> [vor.tree | (append Sorts (vor.algebra-sort-names Data))]
  [fol-signature 0 Sorts _ _] -> [vor.tree | Sorts])
(define vor.fol-functions
  [fol-signature 1 _ Functions _ Data] -> (append Functions (vor.algebra-functions Data))
  [fol-signature 0 _ Functions _] -> Functions)
(define vor.fol-predicates
  [fol-signature 1 _ _ Predicates _] -> Predicates
  [fol-signature 0 _ _ Predicates] -> Predicates)
(define vor.fol-sort-list?
  _ [] -> true
  Sorts [S | Rest] -> (and (vor.member? S Sorts) (vor.fol-sort-list? Sorts Rest))
  _ _ -> false)
(define vor.fol-function-names
  [] -> []
  [[Name _ _] | Rest] -> [Name | (vor.fol-function-names Rest)])
(define vor.fol-predicate-names
  [] -> []
  [[Name _] | Rest] -> [Name | (vor.fol-predicate-names Rest)])
(define vor.fol-functions?
  _ [] -> true
  Sorts [[Name Args Result] | Rest] ->
    (and (vor.names? [Name])
      (and (not (vor.member? Name [vor.leaf vor.node]))
        (and (vor.fol-sort-list? Sorts Args)
          (and (vor.member? Result Sorts)
            (and (not (= Result vor.tree)) (vor.fol-functions? Sorts Rest))))))
  _ _ -> false)
(define vor.fol-predicates?
  _ [] -> true
  Sorts [[Name Args] | Rest] ->
    (and (vor.names? [Name])
      (and (vor.fol-sort-list? Sorts Args) (vor.fol-predicates? Sorts Rest)))
  _ _ -> false)
(define vor.fol-signature?
  [fol-signature 1 Sorts Functions Predicates Data] ->
    (and (vor.algebra-declarations? Sorts Data)
      (vor.fol-signature? [fol-signature 0 (append Sorts (vor.algebra-sort-names Data))
        (append Functions (vor.algebra-functions Data)) Predicates]))
  [fol-signature 0 Sorts Functions Predicates] ->
    (and (vor.names? Sorts)
      (and (vor.unique? Sorts)
        (and (not (vor.member? vor.tree Sorts))
          (and (vor.fol-functions? [vor.tree | Sorts] Functions)
            (and (vor.unique? (vor.fol-function-names Functions))
              (and (vor.fol-predicates? [vor.tree | Sorts] Predicates)
                   (vor.unique? (vor.fol-predicate-names Predicates))))))))
  _ -> false)

(define vor.fol-function
  Name [[Name Args Result] | _] -> [function Args Result]
  Name [_ | Rest] -> (vor.fol-function Name Rest)
  _ [] -> missing)
(define vor.fol-predicate
  Name [[Name Args] | _] -> [predicate Args]
  Name [_ | Rest] -> (vor.fol-predicate Name Rest)
  _ [] -> missing)
(define vor.fol-at
  [X | _] 0 -> [found X]
  [_ | Rest] N -> (vor.fol-at Rest (- N 1)) where (> N 0)
  _ _ -> missing)
(define vor.fol-var-sort
  [found S] -> [sort S]
  _ -> invalid)

(define vor.fol-term-sort
  _ Vars [v N] ->
    (if (vor.nat? N) (vor.fol-var-sort (vor.fol-at Vars N)) invalid)
  _ _ [app vor.leaf []] -> [sort vor.tree]
  Sig Vars [app vor.node [Left Right]] ->
    (if (and (= (vor.fol-term-sort Sig Vars Left) [sort vor.tree])
             (= (vor.fol-term-sort Sig Vars Right) [sort vor.tree]))
      [sort vor.tree] invalid)
  Sig Vars [app Name Args] ->
    (vor.fol-call-sort Sig Vars Args (vor.fol-function Name (vor.fol-functions Sig)))
  _ _ _ -> invalid)
(define vor.fol-call-sort
  Sig Vars Args [function Sorts Result] ->
    (if (vor.fol-arguments? Sig Vars Args Sorts) [sort Result] invalid)
  _ _ _ _ -> invalid)
(define vor.fol-arguments?
  _ _ [] [] -> true
  Sig Vars [Arg | Args] [Sort | Sorts] ->
    (and (= (vor.fol-term-sort Sig Vars Arg) [sort Sort])
         (vor.fol-arguments? Sig Vars Args Sorts))
  _ _ _ _ -> false)
(define vor.fol-predicate-args?
  Sig Vars Args [predicate Sorts] -> (vor.fol-arguments? Sig Vars Args Sorts)
  _ _ _ _ -> false)

(define vor.fol-formula?
  _ _ [top] -> true
  _ _ [bottom] -> true
  Sig Vars [pred Name Args] ->
    (vor.fol-predicate-args? Sig Vars Args
      (vor.fol-predicate Name (vor.fol-predicates Sig)))
  Sig Vars [equal Sort Left Right] ->
    (and (vor.member? Sort (vor.fol-sorts Sig))
      (and (= (vor.fol-term-sort Sig Vars Left) [sort Sort])
           (= (vor.fol-term-sort Sig Vars Right) [sort Sort])))
  Sig Vars [and P Q] -> (and (vor.fol-formula? Sig Vars P) (vor.fol-formula? Sig Vars Q))
  Sig Vars [or P Q] -> (and (vor.fol-formula? Sig Vars P) (vor.fol-formula? Sig Vars Q))
  Sig Vars [imp P Q] -> (and (vor.fol-formula? Sig Vars P) (vor.fol-formula? Sig Vars Q))
  Sig Vars [forall Sort P] ->
    (and (vor.member? Sort (vor.fol-sorts Sig)) (vor.fol-formula? Sig [Sort | Vars] P))
  Sig Vars [exists Sort P] ->
    (and (vor.member? Sort (vor.fol-sorts Sig)) (vor.fol-formula? Sig [Sort | Vars] P))
  _ _ _ -> false)
(define vor.fol-context?
  _ _ [] -> true
  Sig Vars [P | Rest] ->
    (and (vor.fol-formula? Sig Vars P) (vor.fol-context? Sig Vars Rest))
  _ _ _ -> false)
(define vor.fol-sequent?
  Sig Vars Gamma P ->
    (and (vor.fol-signature? Sig)
      (and (vor.fol-sort-list? (vor.fol-sorts Sig) Vars)
        (and (vor.fol-context? Sig Vars Gamma) (vor.fol-formula? Sig Vars P)))))

\\ Internal operations consume formed syntax. Public calls validate first.
(define vor.fol-shift-term
  [v N] Amount Cut -> [v (if (>= N Cut) (+ N Amount) N)]
  [app Name Args] Amount Cut -> [app Name (vor.fol-shift-terms Args Amount Cut)])
(define vor.fol-shift-terms
  [] _ _ -> []
  [T | Ts] Amount Cut ->
    [(vor.fol-shift-term T Amount Cut) | (vor.fol-shift-terms Ts Amount Cut)])
(define vor.fol-shift
  [top] _ _ -> [top]
  [bottom] _ _ -> [bottom]
  [pred Name Args] A C -> [pred Name (vor.fol-shift-terms Args A C)]
  [equal Sort L R] A C -> [equal Sort (vor.fol-shift-term L A C) (vor.fol-shift-term R A C)]
  [and P Q] A C -> [and (vor.fol-shift P A C) (vor.fol-shift Q A C)]
  [or P Q] A C -> [or (vor.fol-shift P A C) (vor.fol-shift Q A C)]
  [imp P Q] A C -> [imp (vor.fol-shift P A C) (vor.fol-shift Q A C)]
  [forall S P] A C -> [forall S (vor.fol-shift P A (+ C 1))]
  [exists S P] A C -> [exists S (vor.fol-shift P A (+ C 1))])
(define vor.fol-shift-context
  [] _ -> []
  [P | Ps] A -> [(vor.fol-shift P A 0) | (vor.fol-shift-context Ps A)])

\\ Remove binder Depth. Shift the replacement beneath nested binders, and
\\ decrement indices above the removed binder. Never capture a free variable.
(define vor.fol-sub-term
  [v N] T Depth -> (vor.fol-shift-term T Depth 0) where (= N Depth)
  [v N] _ Depth -> [v (if (> N Depth) (- N 1) N)]
  [app Name Args] T Depth -> [app Name (vor.fol-sub-terms Args T Depth)])
(define vor.fol-sub-terms
  [] _ _ -> []
  [A | As] T D -> [(vor.fol-sub-term A T D) | (vor.fol-sub-terms As T D)])
(define vor.fol-sub
  [top] _ _ -> [top]
  [bottom] _ _ -> [bottom]
  [pred Name Args] T D -> [pred Name (vor.fol-sub-terms Args T D)]
  [equal S L R] T D -> [equal S (vor.fol-sub-term L T D) (vor.fol-sub-term R T D)]
  [and P Q] T D -> [and (vor.fol-sub P T D) (vor.fol-sub Q T D)]
  [or P Q] T D -> [or (vor.fol-sub P T D) (vor.fol-sub Q T D)]
  [imp P Q] T D -> [imp (vor.fol-sub P T D) (vor.fol-sub Q T D)]
  [forall S P] T D -> [forall S (vor.fol-sub P T (+ D 1))]
  [exists S P] T D -> [exists S (vor.fol-sub P T (+ D 1))])

(define vor.fol-instantiate
  Sig Vars Sort Body Term ->
    (if (vor.fol-signature? Sig)
      (if (and (vor.fol-sort-list? (vor.fol-sorts Sig) Vars)
        (and (vor.member? Sort (vor.fol-sorts Sig))
          (and (vor.fol-formula? Sig [Sort | Vars] Body)
               (= (vor.fol-term-sort Sig Vars Term) [sort Sort]))))
        [ok (vor.fol-sub Body Term 0)]
        [rejected malformed-instantiation])
      [rejected malformed-signature]))
