\\ Authoritative one-request finite protocol. Durable facts survive crashes.
\\ Lease ownership is abstract: concrete worker/epoch/tenant refinement is OPEN.
(define effects.invariant
  -> [conj [disj [neg [var accepted]] [conj [var mutation] [disj [var obligation] [var completed]]]]
      [conj [disj [neg [var responded]] [var accepted]]
       [conj [disj [neg [var effect]] [var accepted]]
        [conj [disj [neg [var completed]] [conj [var effect] [neg [var obligation]]]]
         [conj [disj [neg [var ack]] [var effect]]
          [conj [disj [neg [var lease]] [var obligation]] [neg [var duplicate]]]]]]]])
(define effects.rules
  -> [[rule request-commit [neg [var accepted]]
       [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
      [rule respond [conj [var accepted] [var mutation]] [[responded [lit true]]]]
      [rule claim [conj [var obligation] [neg [var lease]]]
       [[lease [lit true]] [expired [lit false]] [ack [lit false]]]]
      [rule expire [var lease] [[lease [lit false]] [expired [lit true]] [ack [lit false]]]]
      [rule apply-effect [conj [var lease] [conj [var obligation] [neg [var expired]]]]
       [[effect [lit true]] [ack [lit false]]]]
      [rule acknowledge [conj [var lease] [conj [var effect] [neg [var ack]]]] [[ack [lit true]]]]
      [rule lose-ack [conj [var lease] [conj [var effect] [neg [var ack]]]] [[ack [lit false]]]]
      [rule crash [var lease] [[lease [lit false]] [expired [lit true]] [ack [lit false]]]]
      [rule finish [conj [var lease] [conj [var effect] [var ack]]]
       [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]]])
(define effects.with-rules
  Rules -> [vor-model 0 [accepted mutation obligation responded lease expired effect ack completed duplicate]
    [[false false false false false false false false false false]] Rules (effects.invariant)])
(define effects.model -> (effects.with-rules (effects.rules)))

\\ Mutate exactly one rule; all other actions and the invariant remain identical.
(define effects.replace
  _ _ [] -> []
  Label Replacement [[rule Label _ _] | Rest] -> [Replacement | Rest]
  Label Replacement [Rule | Rest] -> [Rule | (effects.replace Label Replacement Rest)])
(define effects.mutant-commit
  -> (effects.with-rules (effects.replace request-commit
      [rule request-commit [neg [var accepted]] [[accepted [lit true]] [obligation [lit true]]]] (effects.rules))))
(define effects.mutant-finish
  -> (effects.with-rules (effects.replace finish
      [rule finish [var lease] [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]] (effects.rules))))
(define effects.mutant-duplicate
  -> (effects.with-rules (effects.replace apply-effect
      [rule apply-effect [conj [var lease] [conj [var obligation] [neg [var expired]]]]
       [[effect [lit true]] [ack [lit false]] [duplicate [var effect]]]] (effects.rules))))
(define effects.mutant-lost-work
  -> (effects.with-rules (effects.replace crash
      [rule crash [var lease] [[lease [lit false]] [expired [lit true]] [ack [lit false]] [obligation [lit false]]]] (effects.rules))))
(define effects.emit -> (print (effects.model)))
