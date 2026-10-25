(load "vor.shen")
(load "adapters/fenced-profile.shen")
(load "adapters/shencheck.shen")
(load "adapters/history-producer.shen")
(load "adapters/history-checker.shen")
(define hc.assert true _ -> true false Why -> (simple-error (str Why)))
(hc.assert (= (fj.session-start) [accepted total-admission]) admission)
(define hc.extract [produced E] -> E X -> X)
(define hc.cert H -> (hc.extract (fj.produce H 512 100000)))
(define hc.check H -> (fj.check-history (hc.cert H)))
(define hc.good -> [fj-history 0
  [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
   [fj-op 2 fj-b-claim-w1-pa [] applied allow]]
  [[fj-effect 1 applied] [fj-effect 2 applied]]
  [fj-final [fj-snapshot 0 [fj-pair fj-run-w1-e0-live-pa fj-run-w1-e0-live-pa] [0 0 0] [0 0 0]]]])
(hc.assert (= (hc.check (hc.good)) [checked finite-history-consistency]) concurrent-two-tenant)
(define hc.drop-edge [fj-evidence V H [fj-dag D N [_ | Es] R]] -> [fj-evidence V H [fj-dag D N Es R]])
(hc.assert (= (fj.check-history (hc.drop-edge (hc.cert (hc.good)))) [rejected outgoing-coverage]) omitted-edge)
(define hc.root-rem [fj-evidence V H [fj-dag D [[fj-node 0 W _ B] | Ns] Es R]] -> [fj-evidence V H [fj-dag D [[fj-node 0 W [] B] | Ns] Es R]])
(hc.assert (= (fj.check-history (hc.root-rem (hc.cert (hc.good)))) [rejected root-remaining]) forged-root-remaining)
(define hc.duplicate-edge [fj-evidence V H [fj-dag D N [E | Es] R]] -> [fj-evidence V H [fj-dag D N [E E | Es] R]])
(hc.assert (= (fj.check-history (hc.duplicate-edge (hc.cert (hc.good)))) [rejected duplicate-node-or-edge]) duplicate-edge)
(define hc.bad-target [fj-evidence V H [fj-dag D N [[fj-edge F _ O B] | Es] R]] -> [fj-evidence V H [fj-dag D N [[fj-edge F 0 O B] | Es] R]])
(hc.assert (= (fj.check-history (hc.bad-target (hc.cert (hc.good)))) [rejected missing-edge]) wrong-target)
(hc.assert (= (hc.check [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] unknown unknown]] []
  [fj-final [fj-pair fj-run-w1-e0-live-pa fj-free]]]) [unknown unresolved-observation]) preserve-unknown)
(hc.assert (= (hc.check [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] not-applied allow]] [[fj-effect 1 not-applied]]
  [fj-final [fj-pair fj-free fj-free]]]) [violation bad-terminal]) early-ack-before-durability)
(hc.assert (= (hc.check [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] applied deny]
 [fj-op 2 fj-b-claim-w1-pa [1] applied allow]] [[fj-effect 1 applied] [fj-effect 2 applied]]
 [fj-final [fj-pair fj-run-w1-e0-live-pa fj-run-w1-e0-live-pa]]]) [violation bad-terminal]) sticky-bad)
(hc.assert (= (hc.check [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] applied allow]] [[fj-effect 1 applied]]
 [fj-final [fj-snapshot 0 [fj-pair fj-run-w1-e0-live-pa fj-free] [0 0 2] [0 0 0]]]])
 [violation impossible-observation]) preserve-physical-duplicate-count)
(hc.assert (= (hc.check [fj-history 0 [] [] missing]) [unknown missing-final-observation]) no-observation)
(define hc.replace-history
  [fj-evidence V _ D] H -> [fj-evidence V H D])
(hc.assert (= (fj.check-history (hc.replace-history (hc.cert (hc.good))
 [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [2] applied allow]
 [fj-op 2 fj-b-claim-w1-pa [1] applied allow]] [] missing]))
 [rejected malformed-certificate]) causal-cycle)
(hc.assert (= (fj.check-history (hc.replace-history (hc.cert (hc.good))
 [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [99] applied allow]] [] missing]))
 [rejected malformed-certificate]) nonexistent-predecessor)
(hc.assert (= (fj.check-history (hc.replace-history (hc.cert (hc.good))
 [fj-history 0 [[fj-op 1 artifact-selected-code [] applied allow]] [] missing]))
 [rejected malformed-certificate]) closed-model-actions)
(hc.assert (= (fj.check-history (hc.replace-history (hc.cert (hc.good))
 [fj-history 0 [[fj-op 1 fj-a-claim-w1-pa [] applied allow]]
 [[fj-effect 1 applied] [fj-effect 1 applied]] missing]))
 [rejected malformed-certificate]) duplicate-observation)
(hc.assert (= (hc.check [fj-history 0
 [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
 [fj-op 2 fj-expire [1] applied allow]
 [fj-op 3 fj-a-claim-w1-pa [2] applied allow]
 [fj-op 4 fj-a-complete-w1-e0-pa-op0 [3] applied allow]]
 [[fj-effect 1 applied] [fj-effect 2 applied] [fj-effect 3 applied] [fj-effect 4 applied]]
 [fj-final [fj-pair fj-run-w1-e1-live-pa fj-free]]])
 [violation bad-terminal]) same-owner-stale-epoch)
(hc.assert (= (hc.check [fj-history 0
 [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
 [fj-op 2 fj-b-claim-w1-pa [] applied allow]
 [fj-op 3 fj-a-complete-w1-e0-pa-op0 [1 2] applied allow]]
 [[fj-effect 1 applied] [fj-effect 2 applied] [fj-effect 3 applied]]
 [fj-final [fj-pair fj-done-e0-pa-op0-sink0 fj-done-e0-pa-op0-sink0]]])
 [violation impossible-observation]) tenant-omission-observed)
(hc.assert (= (hc.check [fj-history 0
 [[fj-op 1 fj-a-claim-w1-pa [] applied allow]
 [fj-op 2 fj-a-complete-w1-e0-pa-op0 [1] applied allow]
 [fj-op 3 fj-a-deliver-pa [2] applied allow]
 [fj-op 4 fj-a-deliver-pa [3] applied allow]]
 [[fj-effect 1 applied] [fj-effect 2 applied] [fj-effect 3 applied] [fj-effect 4 applied]]
 [fj-final [fj-snapshot 0 [fj-pair fj-done-e0-pa-op0-sink1 fj-free] [1 1 2] [0 0 0]]]])
 [violation impossible-observation]) duplicate-delivery-observed)
(print "history checker: PASS")
