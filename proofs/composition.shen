\\ Generic reusable composition derivation, using only the existing logic.
\\ forall x. (P(x)->Q(x)) -> (Q(x)->R(x)) -> P(x)->R(x).
(tc -)
(define vor.composition-proof
  P Q -> [gen [intro [intro [intro
    [apply Q [hyp 1] [apply P [hyp 2] [hyp 0]]]]]]])
