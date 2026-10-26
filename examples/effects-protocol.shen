\\ A small authoritative request -> effects protocol.
\\ Booleans are abstract durable facts; rule labels are protocol transitions.
(define effects.model
  -> [vor-model 0
      [accepted mutation obligation responded lease expired effect completed]
      [[false false false false false false false false]]
      [[rule request-commit
          [neg [var accepted]]
          [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
       [rule respond
          [conj [var accepted] [conj [var mutation] [var obligation]]]
          [[responded [lit true]]]]
       [rule claim
          [conj [var obligation] [neg [var lease]]]
          [[lease [lit true]] [expired [lit false]]]]
       [rule expire
          [var lease]
          [[lease [lit false]] [expired [lit true]]]]
       [rule apply-effect
          [conj [var lease] [neg [var expired]]]
          [[effect [lit true]]]]
       [rule finish
          [conj [var lease] [conj [var effect] [neg [var expired]]]]
          [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]]]
      [conj [disj [neg [var responded]] [var mutation]]
        [conj [disj [neg [var effect]] [var mutation]]
          [disj [neg [var completed]] [var effect]]]]])

\\ Deliberately broken implementations used to prove the checker is non-vacuous.
(define effects.broken-commit
  -> [vor-model 0
      [accepted mutation obligation responded lease expired effect completed]
      [[false false false false false false false false]]
      [[rule request-commit [neg [var accepted]]
          [[accepted [lit true]] [obligation [lit true]]]]
       [rule respond [conj [var accepted] [var obligation]]
          [[responded [lit true]]]]]
      [conj [disj [neg [var responded]] [var mutation]]
        [conj [disj [neg [var effect]] [var mutation]]
          [disj [neg [var completed]] [var effect]]]]])

(define effects.broken-finish
  -> [vor-model 0
      [accepted mutation obligation responded lease expired effect completed]
      [[false false false false false false false false]]
      [[rule request-commit [neg [var accepted]]
          [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
       [rule claim [conj [var obligation] [neg [var lease]]]
          [[lease [lit true]] [expired [lit false]]]]
       [rule finish [var lease] [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]]]
      [conj [disj [neg [var responded]] [var mutation]]
        [conj [disj [neg [var effect]] [var mutation]]
          [disj [neg [var completed]] [var effect]]]]])

(define effects.brokencommit -> (effects.broken-commit))
(define effects.brokenfinish -> (effects.broken-finish))

(define effects.emit
  -> (print (effects.model)))
