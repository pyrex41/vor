(load "vor.shen")
(load "adapters/fenced-profile.shen")
(load "adapters/history-producer.shen")
(define hp-test.assert
  true _ -> true
  false Why -> (simple-error (str Why)))
(hp-test.assert (= (fj.session-start) [accepted total-admission]) admission)
(define hp-two -> [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
   [fj-op 2 fj-b-claim-w1-pa [] applied allow]]
  [[fj-effect 1 applied] [fj-effect 2 applied]] opaque-final-facts])
(define hp-node-count
  [produced [fj-evidence _ _ [fj-dag _ Nodes _ _]]] -> (length Nodes)
  _ -> 0)
(let R (fj.produce (hp-two) 512 100)
  (hp-test.assert (= (hp-node-count R) 4) two-independent))
(let R (fj.produce [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] unknown allow]] [] facts] 512 100)
  (do (hp-test.assert (= R (fj.produce [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] unknown allow]] [] facts] 512 100)) deterministic)
      (hp-test.assert (= (hp-node-count R) 3) unknown-observation-completes)))
(hp-test.assert (= (hp-node-count (fj.produce [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] unknown allow]]
  [[fj-effect 1 not-applied]] facts] 512 100)) 2) known-observation-filters)
(hp-test.assert (= (hp-node-count (fj.produce [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
   [fj-op 2 fj-a-complete-w1-e0-pa-op0 [1] applied allow]]
  [[fj-effect 1 applied] [fj-effect 2 applied]] facts] 512 100)) 3) dependent-eligibility)
(hp-test.assert (= (fj.produce (hp-two) 1 100) [unknown node-budget]) tiny-node-budget)
(print "history producer: PASS")
