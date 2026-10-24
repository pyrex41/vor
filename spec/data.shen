\\ R04: monomorphic, strictly positive initial algebras. Fields are sort names,
\\ never function spaces or proof types. A declaration may refer to itself and
\\ earlier sorts, not later declarations. No mutual or nested recursion yet.
(tc -)
(define vor.algebra-sort-names
  [] -> []
  [[data S _] | Ds] -> [S | (vor.algebra-sort-names Ds)]
  _ -> [invalid invalid])
(define vor.algebra-constructors
  _ [] -> []
  S [[C Fields] | Cs] -> [[C Fields S] | (vor.algebra-constructors S Cs)]
  _ _ -> [[invalid]])
(define vor.algebra-functions
  [] -> []
  [[data S Cs] | Ds] -> (append (vor.algebra-constructors S Cs) (vor.algebra-functions Ds))
  _ -> [[invalid]])
(define vor.algebra-declarations?
  Sorts Data -> (and (vor.names? Sorts) (vor.algebra-declarations-from? [vor.tree | Sorts] Data)))
(define vor.algebra-declarations-from?
  _ [] -> true
  Earlier [[data S Cs] | Ds] ->
    (and (vor.names? [S])
      (and (not (vor.member? S Earlier))
        (and (not (= Cs []))
          (and (vor.algebra-fields? [S | Earlier] Cs)
            (and (vor.algebra-base? S Cs)
              (vor.algebra-declarations-from? [S | Earlier] Ds))))))
  _ _ -> false)
(define vor.algebra-fields?
  _ [] -> true
  Sorts [[C Fields] | Cs] ->
    (and (vor.names? [C])
      (and (vor.fol-sort-list? Sorts Fields) (vor.algebra-fields? Sorts Cs)))
  _ _ -> false)
(define vor.algebra-base?
  S [[_ Fields] | Cs] -> (or (not (vor.member? S Fields)) (vor.algebra-base? S Cs))
  _ [] -> false)
(define vor.algebra-data
  S [fol-signature 1 _ _ _ Data] -> (vor.algebra-find S Data)
  _ _ -> missing)
(define vor.algebra-find
  S [[data S Cs] | _] -> [constructors Cs]
  S [_ | Ds] -> (vor.algebra-find S Ds)
  _ [] -> missing)
(define vor.algebra-constructor
  C [fol-signature 1 _ _ _ Data] -> (vor.fol-function C (vor.algebra-functions Data))
  _ _ -> missing)

\\ Values encode a nullary constructor as its symbol, others as [C field ...].
\\ Thus values remain in R03's inert domain and VOR-DATA/0, without host numbers.
(define vor.algebra-value-term
  Sig Sort Value ->
    (vor.algebra-value-with Sig Sort Value (vor.algebra-data Sort Sig)))
(define vor.algebra-value-with
  Sig Sort Value [constructors Cs] -> (vor.algebra-value-choose Sig Sort Value Cs)
  _ _ _ _ -> invalid)
(define vor.algebra-value-choose
  _ _ C [[C []] | _] -> [term [app C []]]
  Sig Sort [C | Values] [[C Fields] | _] ->
    (if (not (= Fields [])) (vor.algebra-value-fields Sig C Fields Values) invalid)
  Sig Sort V [_ | Cs] -> (vor.algebra-value-choose Sig Sort V Cs)
  _ _ _ [] -> invalid)
(define vor.algebra-value-fields
  Sig C Fields Values -> (vor.algebra-value-finish C (vor.algebra-value-terms Sig Fields Values)))
(define vor.algebra-value-finish
  C [terms Ts] -> [term [app C Ts]]
  _ _ -> invalid)
(define vor.algebra-value-terms
  _ [] [] -> [terms []]
  Sig [S | Ss] [V | Vs] ->
    (vor.algebra-value-next (vor.algebra-value-term Sig S V) (vor.algebra-value-terms Sig Ss Vs))
  _ _ _ -> invalid)
(define vor.algebra-value-next
  [term T] [terms Ts] -> [terms [T | Ts]]
  _ _ -> invalid)
(define vor.algebra-value?
  Sig Sort V -> (trap-error (not (= (vor.algebra-value-term Sig Sort V) invalid)) (/. E false)))
(define vor.algebra-term-value
  [app C []] -> C
  [app C Ts] -> [C | (map (function vor.algebra-term-value) Ts)])

\\ A reusable monomorphic standard universe. Lists here contain naturals;
\\ another element sort requires its own declaration/constructor names.
(define vor.standard-data
  -> [[data natural [[zero []] [succ [natural]]]]
      [data integer [[nonnegative [natural]] [negative [natural]]]]
      [data boolean [[bool.false []] [bool.true []]]]
      [data nat-list [[nil []] [cell [natural nat-list]]]]
      [data nat-product [[tuple [natural natural]]]]
      [data nat-sum [[sum.left [natural]] [sum.right [natural]]]]])
(define vor.standard-signature -> [fol-signature 1 [] [] [] (vor.standard-data)])
(define vor.algebra-root-inventory
  -> [vor-algebra-root 1 [data-induct inject disjoint]
       [finite-initial-algebras strictly-positive monomorphic inhabited ordered-declarations]])
