\\ Untrusted proof-term builders. No arithmetic oracle or host numeric result
\\ enters a derivation. Every output is checked by the first-order kernel.
(tc -)
(define vor.proof-specialize
  _ [] E -> E
  [forall S Body] [T | Ts] E ->
    (vor.proof-specialize (vor.fol-sub Body T 0) Ts [inst S Body T E]))
(define vor.proof-cong
  Sort C L R E ->
    [subst Sort [equal Sort [app C [(vor.fol-shift-term L 1 0)]] [app C [[v 0]]]] L R E [refl]])
(define vor.arithmetic-zero -> [app zero []])
(define vor.arithmetic-succ T -> [app succ [T]])
(define vor.arithmetic-add Name A B -> [app Name [A B]])
(define vor.arithmetic-zero-equation
  Name -> [forall natural [equal natural [app Name [[app zero []] [v 0]]] [v 0]]])
(define vor.arithmetic-step-equation
  Name -> (vor.quantify [natural natural]
    [equal natural [app Name [[app succ [[v 0]]] [v 1]]]
      [app succ [[app Name [[v 0] [v 1]]]]]]))
(define vor.arithmetic-right-zero-body
  Name -> [equal natural [app Name [[v 0] [app zero []]]] [v 0]])
(define vor.arithmetic-right-zero
  Name BaseIndex StepIndex ->
    [data-induct
      [[zero (vor.proof-specialize (vor.arithmetic-zero-equation Name)
               [(vor.arithmetic-zero)] [hyp BaseIndex])]
       [succ [trans [app succ [[app Name [[v 0] [app zero []]]]]]
         (vor.proof-specialize (vor.arithmetic-step-equation Name)
           [(vor.arithmetic-zero) [v 0]] [hyp (+ StepIndex 1)])
         (vor.proof-cong natural succ [app Name [[v 0] [app zero []]]] [v 0] [hyp 0])]]]])

\\ Exact integers use nonnegative(n)=n, negative(n)=-(n+1). There is one zero.
\\ These operations manipulate constructors only; no float/host integer path.
(define vor.peano-add
  zero B -> B
  [succ A] B -> [succ (vor.peano-add A B)])
(define vor.integer-cancel
  zero zero -> [nonnegative zero]
  zero [succ B] -> [negative B]
  [succ A] zero -> [nonnegative [succ A]]
  [succ A] [succ B] -> (vor.integer-cancel A B))
(define vor.integer-add
  [nonnegative A] [nonnegative B] -> [nonnegative (vor.peano-add A B)]
  [negative A] [negative B] -> [negative [succ (vor.peano-add A B)]]
  [nonnegative A] [negative B] -> (vor.integer-cancel A [succ B])
  [negative A] [nonnegative B] -> (vor.integer-cancel B [succ A]))
\\ A concrete receipt is separate from generic arithmetic lemmas. It checks
\\ constructor recursion, never accepts a purported Boolean proof flag.
(define vor.check-integer-add
  A B C [integer-add 0 A B C] ->
    (trap-error
      (if (and (vor.algebra-value? (vor.standard-signature) integer A)
        (and (vor.algebra-value? (vor.standard-signature) integer B)
             (vor.algebra-value? (vor.standard-signature) integer C)))
        (if (= C (vor.integer-add A B)) [accepted exact-integer-sum] [rejected integer-sum])
        [rejected integer-domain])
      (/. E [unknown integer-checker-error]))
  _ _ _ _ -> [rejected integer-identity])
(define vor.boolean-encode
  true -> bool.true
  false -> bool.false)
(define vor.boolean-decode
  bool.true -> [value true]
  bool.false -> [value false]
  _ -> [rejected boolean-domain])
