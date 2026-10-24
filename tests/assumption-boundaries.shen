\\ A healthy final state cannot erase an illegal intermediate effect.
(define test.transient-model
  -> [vor-model 0 [bad] [[false]]
       [[rule damage [neg [var bad]] [[bad [lit true]]]]
        [rule repair [var bad] [[bad [lit false]]]]]
       [neg [var bad]]])
(test.equal final-state-healthy (vor.safe? (test.transient-model) [false]) true)
(test.equal intermediate-violation-retained
  (vor.trace (test.transient-model)
    [[initial [false]] [step damage [true]] [step repair [false]]])
  [violation invariant 1 [true]])
\\ Partial evidence retains safe AND unsafe explanations; consistent is not safe.
(test.equal ambiguous-observation-not-proof
  (vor.observe (test.transient-model) [[false] [true]] repair [] 2)
  [consistent [[false]]])
(test.equal arbitrary-belief-is-not-reachability
  (vor.observe [vor-model 0 [x] [[false]] [[rule stay [lit true] []]] [neg [var x]]]
    [[false] [true]] stay [] 2)
  [consistent [[true] [false]]])
