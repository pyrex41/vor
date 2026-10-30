\\ Untrusted derived structural equality. For declared algebras it emits
\\ ordinary inert R03 source definitions (a truth conjunction, constructor
\\ tests, field projections and one equality per sort), their [top]
\\ contracts, and the reflexivity and soundness lemmas with proof scripts for
\\ construct/cases.shen. Nothing here is trusted: the definitions are
\\ normalized, constructed and admitted like hand-written source, and every
\\ lemma is rechecked by vor.check-constructed-theorem. No eq primitive and
\\ no axiom is introduced.
(tc -)

\\ [derived-eq Definitions Contracts Lemmas] or [rejected Why].
\\ Truth = [TruthSort Yes No], a declared sort with exactly these two nullary
\\ constructors. Sorts are derived in the given order; every field sort must
\\ be the sort itself or derived earlier, and TruthSort must be listed if a
\\ field uses it.
(define vor.derive-eq
  Data [T Yes No] Sorts ->
    (if (vor.derive-eq-truth? Data [T Yes No])
      (vor.derive-eq-sorts Data [T Yes No] Sorts [] [derive.and] [] [])
      [rejected derived-eq-truth])
  _ _ _ -> [rejected derived-eq-truth])
(define vor.derive-eq-truth?
  Data [T Yes No] -> (= (vor.algebra-find T Data) [constructors [[Yes []] [No []]]]))

(define vor.derive-eq-name S -> (concat derive.eq. S))
(define vor.derive-is-name C -> (concat derive.is. C))
(define vor.derive-get-name C I -> (intern (cn "derive.get." (cn (str C) (cn "." (str I))))))
(define vor.derive-var I -> (intern (cn "X" (str I))))
(define vor.derive-other -> (intern "Other"))

\\ Source helpers: nullary constructors are symbols, others cons spines.
(define vor.derive-cons
  C [] -> C
  C Fields -> [cons C (vor.derive-spine Fields)])
(define vor.derive-spine
  [] -> []
  [F | Fs] -> [cons F (vor.derive-spine Fs)])
(define vor.derive-vars
  0 _ -> []
  N I -> [(vor.derive-var I) | (vor.derive-vars (- N 1) (+ I 1))])
(define vor.derive-pattern
  [C Fields] -> (vor.derive-cons C (vor.derive-vars (length Fields) 1)))

\\ A closed value of each sort: its first constructor without a self field,
\\ fields filled recursively (earlier sorts only, so this terminates).
(define vor.derive-default
  Data S -> (vor.derive-default-of Data S (vor.algebra-find S Data)))
(define vor.derive-default-of
  Data S [constructors Cs] -> (vor.derive-default-ctor Data S Cs)
  _ S _ -> (simple-error (make-string "derive-eq: undeclared sort ~A" S)))
(define vor.derive-default-ctor
  Data S [[C Fields] | Cs] ->
    (if (element? S Fields)
      (vor.derive-default-ctor Data S Cs)
      (vor.derive-cons C (map (/. F (vor.derive-default Data F)) Fields))))

(define vor.derive-and-definition
  [T Yes No] Cs ->
    [define derive.and | (vor.derive-and-clauses Yes No Cs)])
(define vor.derive-and-clauses
  _ _ [] -> []
  Yes No [[Yes []] | Cs] -> [Yes (intern "B") -> (intern "B") | (vor.derive-and-clauses Yes No Cs)]
  Yes No [[C []] | Cs] -> [C (intern "B") -> No | (vor.derive-and-clauses Yes No Cs)])

(define vor.derive-is-definition
  [_ Yes No] Cs C ->
    [define (vor.derive-is-name C) |
      (vor.derive-mapcan (/. D [(vor.derive-pattern D) -> (if (= (hd D) C) Yes No)]) Cs)])
(define vor.derive-get-definition
  Data Cs C I F ->
    [define (vor.derive-get-name C I) |
      (vor.derive-mapcan (/. D [(vor.derive-pattern D) ->
                     (if (= (hd D) C) (vor.derive-var I) (vor.derive-default Data F))]) Cs)])
(define vor.derive-eq-definition
  S Cs ->
    [define (vor.derive-eq-name S) |
      (vor.derive-mapcan (/. D [(vor.derive-pattern D) (vor.derive-other) -> (vor.derive-eq-body D)]) Cs)])
(define vor.derive-eq-body
  [C []] -> [(vor.derive-is-name C) (vor.derive-other)]
  [C Fields] -> [derive.and [(vor.derive-is-name C) (vor.derive-other)]
                  (vor.derive-eq-fields C Fields 1)])
(define vor.derive-eq-fields
  C [F] I -> (vor.derive-eq-field C F I)
  C [F | Fs] I -> [derive.and (vor.derive-eq-field C F I) (vor.derive-eq-fields C Fs (+ I 1))])
(define vor.derive-eq-field
  C F I -> [(vor.derive-eq-name F) (vor.derive-var I)
            [(vor.derive-get-name C I) (vor.derive-other)]])

\\ Lemmas: reflexivity, then soundness, per sort, in derivation order.
(define vor.derive-refl
  [T Yes _] S -> [forall S [equal T [app (vor.derive-eq-name S) [[v 0] [v 0]]] [app Yes []]]])
(define vor.derive-sound
  [T Yes _] S ->
    [forall S [forall S
      [imp [equal T [app (vor.derive-eq-name S) [[v 1] [v 0]]] [app Yes []]]
           [equal S [v 1] [v 0]]]]])

(define vor.derive-eq-sorts
  Data Truth [] Done _ Defs Contracts ->
    [derived-eq
      [(vor.derive-and-definition Truth (vor.derive-truth-ctors Data Truth)) | Defs]
      [[contract derive.and [(hd Truth) (hd Truth)] (hd Truth) 0 [top]] | Contracts]
      (vor.derive-mapcan (/. S [[(vor.derive-refl Truth S) [induct]]
                     [(vor.derive-sound Truth S) [induct induct]]]) Done)]
  Data Truth [S | Ss] Done Names Defs Contracts ->
    (vor.derive-eq-sort Data Truth S Ss Done Names Defs Contracts (vor.algebra-find S Data)))
(define vor.derive-truth-ctors
  Data [T _ _] -> (vor.derive-ctors (vor.algebra-find T Data)))
(define vor.derive-ctors [constructors Cs] -> Cs)
(define vor.derive-eq-sort
  Data Truth S Ss Done Names Defs Contracts [constructors Cs] ->
    (if (and (not (element? S Done)) (vor.derive-fields-ready? S Done Cs))
      (vor.derive-eq-sorts Data Truth Ss (append Done [S]) Names
        (append Defs (vor.derive-sort-definitions Data Truth S Cs))
        (append Contracts (vor.derive-sort-contracts Truth S Cs)))
      [rejected [derived-eq-order S]])
  _ _ S _ _ _ _ _ _ -> [rejected [derived-eq-undeclared S]])
(define vor.derive-fields-ready?
  _ _ [] -> true
  S Done [[_ Fields] | Cs] ->
    (and (vor.derive-every? (/. F (or (= F S) (element? F Done))) Fields)
         (vor.derive-fields-ready? S Done Cs)))
(define vor.derive-every?
  _ [] -> true
  P [X | Xs] -> (and (P X) (vor.derive-every? P Xs)))
(define vor.derive-mapcan
  _ [] -> []
  F [X | Xs] -> (append (F X) (vor.derive-mapcan F Xs)))
(define vor.derive-sort-definitions
  Data Truth S Cs ->
    (append (map (/. C (vor.derive-is-definition Truth Cs (hd C))) Cs)
      (append (vor.derive-mapcan (/. C (vor.derive-gets Data Cs (hd C) (hd (tl C)) 1)) Cs)
        [(vor.derive-eq-definition S Cs)])))
(define vor.derive-gets
  _ _ _ [] _ -> []
  Data Cs C [F | Fs] I -> [(vor.derive-get-definition Data Cs C I F) |
                           (vor.derive-gets Data Cs C Fs (+ I 1))])
(define vor.derive-sort-contracts
  [T Yes No] S Cs ->
    (append (map (/. C [contract (vor.derive-is-name (hd C)) [S] T 0 [top]]) Cs)
      (append (vor.derive-mapcan (/. C (vor.derive-get-contracts S (hd C) (hd (tl C)) 1)) Cs)
        [[contract (vor.derive-eq-name S) [S S] T 0 [top]]])))
(define vor.derive-get-contracts
  _ _ [] _ -> []
  S C [F | Fs] I -> [[contract (vor.derive-get-name C I) [S] F 0 [top]] |
                     (vor.derive-get-contracts S C Fs (+ I 1))])

\\ Top posts for the generated contracts (totality only).
(define vor.derive-top-posts
  Contracts -> (map (/. C (vor.derive-top-post C)) Contracts))
(define vor.derive-top-post
  [contract Name Ins _ _ _] -> [post Name (vor.derive-gens (length Ins))])
(define vor.derive-gens
  0 -> [top]
  N -> [gen (vor.derive-gens (- N 1))])

\\ Proof of lemma K (0-based) of a derived bundle: earlier lemmas are proved
\\ and introduced first, so the proof is closed under the equations alone.
(define vor.derive-lemma-proof
  Sig Eqs Lemmas K Fuel Depth -> (vor.derive-lemma-at Sig Eqs Lemmas K Fuel Depth))
(define vor.derive-lemma-at
  Sig G [[L S] | _] 0 Fuel Depth -> (vor.prove-script-depth Sig [] G L S Fuel Depth)
  Sig G [[L S] | Ls] K Fuel Depth ->
    [apply L [intro (vor.derive-lemma-at Sig [L | G] Ls (- K 1) Fuel Depth)]
      (vor.prove-script-depth Sig [] G L S Fuel Depth)])
