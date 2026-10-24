(tc -)
(test.equal algebra-standard-formation (vor.fol-signature? (vor.standard-signature)) true)
(test.equal algebra-no-negative-occurrence
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data bad [[c [[arrow bad bad]]]]]]]) false)
(test.equal algebra-no-empty-type
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data bad []]]]) false)
(test.equal algebra-no-uninhabited-cycle
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data bad [[again [bad]]]]]]) false)
(test.equal algebra-no-mutual-cycle
  (vor.fol-signature? [fol-signature 1 [] [] []
    [[data a [[a0 []] [ab [b]]]] [data b [[b0 []] [ba [a]]]]]]) false)
(test.equal algebra-no-duplicate-constructor
  (vor.fol-signature? [fol-signature 1 [] [] []
    [[data a [[same []]]] [data b [[same []]]]]]) false)
(test.equal algebra-no-function-constructor-collision
  (vor.fol-signature? [fol-signature 1 [] [[zero [] natural]] [] (vor.standard-data)]) false)
(test.equal algebra-no-reserved-tree
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data vor.tree [[new []]]]]]) false)
(test.equal algebra-no-unknown-fields
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data bad [[new [unknown]]]]]]) false)
(test.equal algebra-no-proof-type
  (vor.fol-signature? [fol-signature 1 [] [] [] [[data bad [[new [[vor-admits x y z]]]]]]]) false)
(test.equal algebra-product (vor.algebra-value? (vor.standard-signature) nat-product [tuple zero [succ zero]]) true)
(test.equal algebra-sum (vor.algebra-value? (vor.standard-signature) nat-sum [sum.right [succ zero]]) true)
(test.equal algebra-list (vor.algebra-value? (vor.standard-signature) nat-list [cell zero [cell [succ zero] nil]]) true)
(test.equal algebra-improper-list (vor.algebra-value? (vor.standard-signature) nat-list [cell zero | nil]) false)
(test.equal algebra-wrong-field (vor.algebra-value? (vor.standard-signature) nat-product [tuple zero nil]) false)
(test.equal algebra-extra-field (vor.algebra-value? (vor.standard-signature) natural [succ zero zero]) false)
(test.equal algebra-noncanonical-nullary (vor.algebra-value? (vor.standard-signature) natural [zero]) false)
(test.equal algebra-float (vor.algebra-value? (vor.standard-signature) natural 1.0) false)
(test.equal algebra-host-integer (vor.algebra-value? (vor.standard-signature) natural 3) false)
(test.equal algebra-negative-zero-is-minus-one
  (vor.integer-add [negative zero] [nonnegative [succ zero]]) [nonnegative zero])
(test.equal algebra-fake-negative-zero (vor.algebra-value? (vor.standard-signature) integer [negative -0.0]) false)
(test.equal bool-embedding-true (vor.boolean-decode (vor.boolean-encode true)) [value true])
(test.equal bool-embedding-false (vor.boolean-decode (vor.boolean-encode false)) [value false])
(test.equal bool-embedding-no-coercion (vor.boolean-decode 1) [rejected boolean-domain])
(define data-test.boolean-theorem
  -> [forall boolean [or [equal boolean [v 0] [app bool.false []]]
                        [equal boolean [v 0] [app bool.true []]]]])
(define data-test.boolean-proof
  -> [data-induct [[bool.false [inl [refl]]] [bool.true [inr [refl]]]]])
(test.equal algebra-boolean-exhaustiveness
  (vor.fol-check (vor.standard-signature) [] [] (data-test.boolean-theorem) (data-test.boolean-proof) 5)
  [accepted first-order-derivation])
(test.equal algebra-indexed-induction
  (vor.fol-typecheck (vor.standard-signature) [] [] (data-test.boolean-theorem) (data-test.boolean-proof))
  [accepted first-order-typed-evidence])
(test.equal algebra-no-missing-branch
  (hd (vor.fol-check (vor.standard-signature) [] [] (data-test.boolean-theorem)
    [data-induct [[bool.false [inl [refl]]]]] 30)) rejected)
(test.equal algebra-no-duplicate-branch
  (hd (vor.fol-check (vor.standard-signature) [] [] (data-test.boolean-theorem)
    [data-induct [[bool.false [inl [refl]]] [bool.false [inl [refl]]]]] 30)) rejected)
(test.equal algebra-no-circular-induction
  (hd (vor.fol-check (vor.standard-signature) [] [] [forall natural [bottom]]
    [data-induct [[zero [hyp 0]] [succ [hyp 0]]]] 30)) rejected)
(test.equal algebra-no-false-conclusion
  (hd (vor.fol-check (vor.standard-signature) [] []
    [forall natural [equal natural [v 0] [app zero []]]]
    [data-induct [[zero [refl]] [succ [hyp 0]]]] 30)) rejected)
(test.equal algebra-no-induct-uninterpreted-sort
  (hd (vor.fol-check [fol-signature 1 [opaque] [] [] (vor.standard-data)] [] []
    [forall opaque [top]] [data-induct []] 30)) rejected)
(test.equal algebra-induction-exhaustion
  (vor.fol-check (vor.standard-signature) [] [] (data-test.boolean-theorem) (data-test.boolean-proof) 4)
  [unknown proof-fuel])
(test.equal algebra-no-eigenvariable-escape
  (hd (vor.fol-check (vor.standard-signature) [natural] []
    [forall natural [equal natural [v 0] [v 1]]]
    [data-induct [[zero [refl]] [succ [hyp 0]]]] 30)) rejected)
(test.equal algebra-induction-frame
  (vor.fol-check (vor.standard-signature) [natural] [[equal natural [v 0] [app zero []]]]
    [forall natural [equal natural [v 1] [app zero []]]]
    [data-induct [[zero [hyp 0]] [succ [hyp 1]]]] 3)
  [accepted first-order-derivation])
(test.equal algebra-disjoint
  (vor.fol-check (vor.standard-signature) [natural]
    [[equal natural [app zero []] [app succ [[v 0]]]]] [bottom]
    [disjoint [app zero []] [app succ [[v 0]]] [hyp 0]] 2)
  [accepted first-order-derivation])
(test.equal algebra-not-disjoint-same-constructor
  (hd (vor.fol-check (vor.standard-signature) [natural]
    [[equal natural [app succ [[v 0]]] [app succ [[v 0]]]]] [bottom]
    [disjoint [app succ [[v 0]]] [app succ [[v 0]]] [hyp 0]] 2)) rejected)
(test.equal algebra-disjoint-needs-equality
  (hd (vor.fol-check (vor.standard-signature) [natural] [] [bottom]
    [disjoint [app zero []] [app succ [[v 0]]] [refl]] 2)) rejected)
(define data-test.cell-left -> [app cell [[v 0] [v 2]]])
(define data-test.cell-right -> [app cell [[v 1] [v 3]]])
(test.equal algebra-injective
  (vor.fol-check (vor.standard-signature) [natural natural nat-list nat-list]
    [[equal nat-list (data-test.cell-left) (data-test.cell-right)]]
    [and [equal natural [v 0] [v 1]] [equal nat-list [v 2] [v 3]]]
    [pair [inject [cell [[v 0] [v 2]] [[v 1] [v 3]]] 0 [hyp 0]]
          [inject [cell [[v 0] [v 2]] [[v 1] [v 3]]] 1 [hyp 0]]] 5)
  [accepted first-order-derivation])
(test.equal algebra-injection-wrong-index
  (hd (vor.fol-check (vor.standard-signature) [natural natural nat-list nat-list]
    [[equal nat-list (data-test.cell-left) (data-test.cell-right)]] [equal natural [v 0] [v 1]]
    [inject [cell [[v 0] [v 2]] [[v 1] [v 3]]] 1 [hyp 0]] 10)) rejected)
(test.equal algebra-injection-unrelated
  (hd (vor.fol-check (vor.standard-signature) [natural natural nat-list nat-list]
    [[equal nat-list (data-test.cell-left) (data-test.cell-left)]] [equal natural [v 0] [v 1]]
    [inject [cell [[v 0] [v 2]] [[v 1] [v 3]]] 0 [hyp 0]] 10)) rejected)
(test.equal algebra-no-injection-of-uninterpreted-function
  (hd (vor.fol-check [fol-signature 1 [] [[f [natural] natural]] [] (vor.standard-data)]
    [natural natural] [[equal natural [app f [[v 0]]] [app f [[v 1]]]]]
    [equal natural [v 0] [v 1]] [inject [f [[v 0]] [[v 1]]] 0 [hyp 0]] 10)) rejected)
\\ Hand-written expected substitution under an algebra binder.
(test.equal algebra-binder-substitution
  (vor.fol-instantiate (vor.standard-signature) [natural] natural
    [forall nat-list [equal natural [v 1] [v 2]]] [app succ [[v 0]]])
  [ok [forall nat-list [equal natural [app succ [[v 1]]] [v 1]]]])

\\ Independent test oracle uses host signed integers ONLY here, with a bounded
\\ correspondence to constructor values. The acceptance path never calls it.
(define data-test.peano
  0 -> zero
  N -> [succ (data-test.peano (- N 1))])
(define data-test.integer
  N -> [nonnegative (data-test.peano N)] where (>= N 0)
  N -> [negative (data-test.peano (- (- 0 N) 1))])
(define data-test.sum-row
  _ 7 -> done
  A B -> (let X (data-test.integer A) Y (data-test.integer B) Z (data-test.integer (+ A B))
    (do (test.equal exact-integer-reference (vor.integer-add X Y) Z)
      (do (test.equal exact-integer-receipt
            (vor.check-integer-add X Y Z [integer-add 0 X Y Z]) [accepted exact-integer-sum])
        (data-test.sum-row A (+ B 1))))))
(define data-test.sum-grid
  7 -> done
  A -> (do (data-test.sum-row A -6) (data-test.sum-grid (+ A 1))))
(data-test.sum-grid -6)
(test.equal integer-wrong-sum
  (vor.check-integer-add [nonnegative zero] [negative zero] [nonnegative zero]
    [integer-add 0 [nonnegative zero] [negative zero] [nonnegative zero]]) [rejected integer-sum])
(test.equal integer-wrong-identity
  (vor.check-integer-add [nonnegative zero] [negative zero] [negative zero]
    [integer-add 0 [nonnegative zero] [nonnegative zero] [negative zero]]) [rejected integer-identity])
(test.equal integer-no-float
  (vor.check-integer-add 0.5 [negative zero] [negative zero]
    [integer-add 0 0.5 [negative zero] [negative zero]]) [rejected integer-domain])
(test.equal integer-no-flag
  (vor.check-integer-add [nonnegative zero] [negative zero] [negative zero] true)
  [rejected integer-identity])
(test.equal algebra-injection-forged-endpoint
  (hd (vor.fol-check (vor.standard-signature) [natural natural nat-list]
    [[equal nat-list [app cell [[v 0] [v 2]]] [app cell [[v 0] [v 2]]]]]
    [equal natural [v 1] [v 0]]
    [inject [cell [[v 0] [v 2]] [[v 0] [v 2]]] 0 [hyp 0]] 10)) rejected)
(test.equal algebra-generic-product-elimination
  (vor.fol-check (vor.standard-signature) [] []
    [forall nat-product [exists natural [exists natural
      [equal nat-product [v 2] [app tuple [[v 1] [v 0]]]]]]]
    [data-induct [[tuple [witness [v 0] [witness [v 1] [refl]]]]]] 4)
  [accepted first-order-derivation])
(test.equal algebra-generic-sum-elimination
  (vor.fol-check (vor.standard-signature) [] []
    [forall nat-sum [or [exists natural [equal nat-sum [v 1] [app sum.left [[v 0]]]]]
                       [exists natural [equal nat-sum [v 1] [app sum.right [[v 0]]]]]]]
    [data-induct [[sum.left [inl [witness [v 0] [refl]]]]
                  [sum.right [inr [witness [v 0] [refl]]]]]] 7)
  [accepted first-order-derivation])
