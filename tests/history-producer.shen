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
(define hp-any-bad
  [] -> false
  [[fj-node _ _ _ true] | _] -> true
  [[fj-node _ _ _ _] | Ns] -> (hp-any-bad Ns)
  _ -> false)
(define hp-result-any-bad
  [produced [fj-evidence _ _ [fj-dag _ Nodes _ _]]] -> (hp-any-bad Nodes)
  _ -> false)
(define hp-edge-count
  [produced [fj-evidence _ _ [fj-dag _ _ Edges _]]] -> (length Edges)
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
(let X (fj.produce [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] applied deny]
   [fj-op 2 fj-b-claim-w1-pa [] applied allow]]
  [[fj-effect 1 applied] [fj-effect 2 applied]] facts] 512 100)
  (hp-test.assert (= (hp-result-any-bad X) true) sticky-bad))
(hp-test.assert (= (hp-result-any-bad (fj.produce [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] not-applied allow]]
  [[fj-effect 1 not-applied]] facts] 512 100)) true) early-ack-bad)
(let R (fj.produce (hp-two) 4 4)
  (do (hp-test.assert (= (hp-node-count R) 4) exact-node-limit)
      (hp-test.assert (= (hp-edge-count R) 4) exact-edge-limit)))
(print "history producer: PASS")
