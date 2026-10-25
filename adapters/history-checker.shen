\\ Independent finite-history certificate checker.  Producers are not trusted.
(tc -)
(define fj.hc-member? _ [] -> false X [X | _] -> true X [_ | Xs] -> (fj.hc-member? X Xs) _ _ -> false)
(define fj.hc-ids [] -> [] [[fj-op I _ _ _ _] | Xs] -> [I | (fj.hc-ids Xs)])
(define fj.hc-node-ids [] -> [] [[fj-node I _ _ _] | Xs] -> [I | (fj.hc-node-ids Xs)])
(define fj.hc-unique? [] -> true [X | Xs] -> (and (not (fj.hc-member? X Xs)) (fj.hc-unique? Xs)))
(define fj.hc-lookup _ [] -> missing I [[fj-op I A P E R] | _] -> [fj-op I A P E R] I [_ | Xs] -> (fj.hc-lookup I Xs))
(define fj.hc-node _ [] -> missing I [[fj-node I W R B] | _] -> [fj-node I W R B] I [_ | Xs] -> (fj.hc-node I Xs))
(define fj.hc-op-id [fj-op I _ _ _ _] -> I)
(define fj.hc-op-action [fj-op _ A _ _ _] -> A)
(define fj.hc-op-preds [fj-op _ _ P _ _] -> P)
(define fj.hc-op-effect [fj-op _ _ _ E _] -> E)
(define fj.hc-op-response [fj-op _ _ _ _ R] -> R)
(define fj.hc-node-id [fj-node I _ _ _] -> I)
(define fj.hc-node-world [fj-node _ W _ _] -> W)
(define fj.hc-node-rem [fj-node _ _ R _] -> R)
(define fj.hc-node-bad [fj-node _ _ _ B] -> B)
(define fj.hc-remove _ [] -> [] X [X | Xs] -> Xs X [Y | Xs] -> [Y | (fj.hc-remove X Xs)])
(define fj.hc-subset? [] _ -> true [X | Xs] Ys -> (and (fj.hc-member? X Ys) (fj.hc-subset? Xs Ys)))
(define fj.hc-status? X -> (or (= X applied) (or (= X not-applied) (= X unknown))))
(define fj.hc-response? X -> (or (= X allow) (or (= X deny) (= X unknown))))
(define fj.hc-operation-id?
  Id -> (and (integer? Id) (and (>= Id 0) (< Id 32))))
(define fj.hc-op? [fj-op I A P E R] -> (and (fj.hc-operation-id? I) (and (vor.algebra-value? (value *fj-session-signature*) fj-action A) (and (vor.proper? P) (and (fj.hc-status? E) (fj.hc-response? R))))) _ -> false)
(define fj.hc-ops? [] -> true [O | Os] -> (and (fj.hc-op? O) (fj.hc-ops? Os)) _ -> false)
(define fj.hc-obs? [] -> true [[fj-effect I S] | Es] -> (and (fj.hc-status? S) (fj.hc-obs? Es)) _ -> false)
(define fj.hc-observation _ [] -> missing I [[fj-effect I S] | _] -> S I [_ | Es] -> (fj.hc-observation I Es))
(define fj.hc-world?
  W -> (vor.algebra-value? (value *fj-session-signature*) fj-world W))
(define fj.hc-preds-free? [] _ -> true [P | Ps] R -> (and (not (fj.hc-member? P R)) (fj.hc-preds-free? Ps R)))
(define fj.hc-eligible? [fj-op I _ P _ _] R -> (and (fj.hc-member? I R) (fj.hc-preds-free? P R)))
(define fj.hc-eligible [] _ -> [] [O | Os] R -> (if (fj.hc-eligible? O R) [O | (fj.hc-eligible Os R)] (fj.hc-eligible Os R)))
(define fj.hc-acyclic? [] _ -> true [[fj-op I _ P _ _] | Os] Ops -> (and (not (fj.hc-member? I P)) (and (not (fj.hc-cycle? P I Ops [])) (fj.hc-acyclic? Os Ops))))
(define fj.hc-cycle? [] _ _ _ -> false [P | Ps] I Ops Seen -> (or (= P I) (or (and (not (fj.hc-member? P Seen)) (fj.hc-cycle? (fj.hc-op-preds (fj.hc-lookup P Ops)) I Ops [P | Seen])) (fj.hc-cycle? Ps I Ops Seen))))
\\ All effect alternatives come from the actual ps-captured mapper. Identity
\\ and the entire operation are checked on return, before observation filtering.
(define fj.hc-branches
  O S -> (fj.hc-mapped
    (shencheck.mapper [sc-observation (fj.hc-op-id O) O [effect (fj.hc-op-effect O)]])
    (fj.hc-op-id O) O S))
(define fj.hc-mapped
  [possibilities Xs] Id O S -> (fj.hc-map-effects Xs Id O S)
  _ _ _ _ -> (simple-error "invalid mapper result"))
(define fj.hc-map-effects
  [] _ _ _ -> []
  [[sc-observation Id O [effect E]] | Xs] Id O S ->
    (if (or (= E applied) (= E not-applied))
      (if (or (= S missing) (or (= S unknown) (= S E)))
        [E | (fj.hc-map-effects Xs Id O S)] (fj.hc-map-effects Xs Id O S))
      (simple-error "invalid mapper effect"))
  _ _ _ _ -> (simple-error "mapper changed identity or payload"))
(define fj.hc-transition [next allow W2] World true B R -> [ok W2 (or B (= R deny))] [next deny _] World true _ _ -> [ok World true] [next allow _] World false B R -> [ok World (or B (or (= R allow) (= R deny)))] [next deny _] World false B R -> [ok World (or B (= R allow))] [unknown R] _ _ _ _ -> [unknown R] [rejected R] _ _ _ _ -> [unknown R] _ _ _ _ _ -> [unknown transition])
(define fj.hc-transition-unknown? [unknown _] -> true _ -> false)
(define fj.hc-find-state _ _ _ [] -> missing W R B [[fj-node I W R B] | _] -> I W R B [_ | Ns] -> (fj.hc-find-state W R B Ns))
(define fj.hc-target [ok W B] O N Ns -> (fj.hc-find-state W (fj.hc-remove O (fj.hc-node-rem N)) B Ns) [unknown _] _ _ _ -> missing)
(define fj.hc-edge? [fj-edge F T O B] -> (or (= B applied) (= B not-applied)) _ -> false)
(define fj.hc-edge?for _ _ _ _ [] -> false F T O B [[fj-edge F T O B] | _] -> true F T O B [_ | Es] -> (fj.hc-edge?for F T O B Es))
(define fj.hc-check-node-ops
  [] _ _ _ _ _ -> [ok]
  [O | Os] N Nodes Ops Obs Edges ->
    (let Bs (fj.hc-branches O (fj.hc-observation (fj.hc-op-id O) Obs))
      Q (fj.hc-check-branches Bs O N Nodes Ops Obs Edges)
      (if (= Q [ok]) (fj.hc-check-node-ops Os N Nodes Ops Obs Edges) Q)))
(define fj.hc-check-branches
  [] _ _ _ _ _ _ -> [ok]
  [B | Bs] O N Nodes Ops Obs Edges ->
    (let X (fj.hc-transition (fj.next (fj.hc-op-action O) (fj.hc-node-world N))
                (fj.hc-node-world N) (= B applied) (fj.hc-node-bad N) (fj.hc-op-response O))
      T (fj.hc-target X (fj.hc-op-id O) N Nodes)
      (if (fj.hc-transition-unknown? X) X
        (if (= T missing) [rejected missing-edge]
        (if (fj.hc-edge?for (fj.hc-node-id N) T (fj.hc-op-id O) B Edges)
          (fj.hc-check-branches Bs O N Nodes Ops Obs Edges)
          [rejected missing-edge])))))
(define fj.hc-expected-count
  [] _ -> 0
  [O | Os] Obs -> (+ (length (fj.hc-branches O (fj.hc-observation (fj.hc-op-id O) Obs)))
                     (fj.hc-expected-count Os Obs)))
(define fj.hc-actual-count
  _ [] -> 0
  Id [[fj-edge Id _ _ _] | Es] -> (+ 1 (fj.hc-actual-count Id Es))
  Id [_ | Es] -> (fj.hc-actual-count Id Es))
(define fj.hc-node-valid?
  [fj-node _ W R B] Ops ->
    (and (fj.hc-world? W)
      (and (vor.proper? R)
        (and (fj.hc-unique? R)
          (and (fj.hc-subset? R (fj.hc-ids Ops))
               (or (= B true) (= B false))))))
  _ _ -> false)
(define fj.hc-check-nodes
  [] _ _ _ _ -> [ok]
  [N | Ns] Nodes Ops Obs Edges ->
    (if (fj.hc-node-valid? N Ops)
      (let Eligible (fj.hc-eligible Ops (fj.hc-node-rem N))
        (if (= (fj.hc-expected-count Eligible Obs) (fj.hc-actual-count (fj.hc-node-id N) Edges))
          (let Q (fj.hc-check-node-ops Eligible N Nodes Ops Obs Edges)
            (if (= Q [ok]) (fj.hc-check-nodes Ns Nodes Ops Obs Edges) Q))
          [rejected outgoing-coverage]))
      [rejected malformed-node]))
(define fj.hc-check-edges
  [] _ _ _ -> [ok]
  [[fj-edge F T O B] | Es] Nodes Ops Obs ->
    (let N (fj.hc-node F Nodes) M (fj.hc-node T Nodes) P (fj.hc-lookup O Ops)
      (if (or (= N missing) (or (= M missing) (= P missing)))
        [rejected bad-edge]
        (if (and (fj.hc-eligible? P (fj.hc-node-rem N))
                 (fj.hc-member? B (fj.hc-branches P (fj.hc-observation O Obs))))
          (let X (fj.hc-transition (fj.next (fj.hc-op-action P) (fj.hc-node-world N))
                     (fj.hc-node-world N) (= B applied) (fj.hc-node-bad N) (fj.hc-op-response P))
            (if (fj.hc-transition-unknown? X) X
              (if (= (fj.hc-target X O N Nodes) T)
              (fj.hc-check-edges Es Nodes Ops Obs)
              [rejected wrong-target])))
          [rejected ineligible-edge])) )
  _ _ _ _ -> [rejected malformed-edge])
(define fj.hc-outgoing _ [] -> [] I [[fj-edge I T _ _] | Es] -> [T | (fj.hc-outgoing I Es)] I [_ | Es] -> (fj.hc-outgoing I Es))
(define fj.hc-reach [] _ Seen -> Seen [I | Q] Nodes Seen -> (if (fj.hc-member? I Seen) (fj.hc-reach Q Nodes Seen) (fj.hc-reach (append Q (fj.hc-outgoing I Nodes)) Nodes [I | Seen])))
(define fj.hc-all-reach? [] _ -> true [N | Ns] Seen -> (and (fj.hc-member? (fj.hc-node-id N) Seen) (fj.hc-all-reach? Ns Seen)))
(define fj.hc-leaves [] -> [] [[fj-node I W [] B] | Ns] -> [[I W B] | (fj.hc-leaves Ns)] [_ | Ns] -> (fj.hc-leaves Ns))
(define fj.hc-counts
  fj-free -> [0 0 0]
  W -> (if (fj.hc-member? W [fj-done-e0-pa-op0-sink0 fj-done-e0-pa-op1-sink0
        fj-done-e0-pb-op0-sink0 fj-done-e0-pb-op1-sink0
        fj-done-e1-pa-op0-sink0 fj-done-e1-pa-op1-sink0
        fj-done-e1-pb-op0-sink0 fj-done-e1-pb-op1-sink0]) [1 1 0]
      (if (fj.hc-member? W [fj-done-e0-pa-op0-sink1 fj-done-e0-pa-op1-sink1
        fj-done-e0-pb-op0-sink1 fj-done-e0-pb-op1-sink1
        fj-done-e1-pa-op0-sink1 fj-done-e1-pa-op1-sink1
        fj-done-e1-pb-op0-sink1 fj-done-e1-pb-op1-sink1]) [1 1 1] [0 0 0])))
(define fj.hc-final-matches?
  [fj-final W] W -> true
  [fj-final [fj-snapshot 0 W CA CB]] W ->
    (fj.hc-world-counts? W CA CB)
  _ _ -> false)
(define fj.hc-world-counts?
  [fj-pair A B] CA CB -> (and (= CA (fj.hc-counts A)) (= CB (fj.hc-counts B)))
  _ _ _ -> false)
(define fj.hc-filter-final
  _ [] -> []
  F [[I W B] | Xs] ->
    (if (fj.hc-final-matches? F W) [[I W B] | (fj.hc-filter-final F Xs)]
      (fj.hc-filter-final F Xs)))
(define fj.hc-all-bad? [] -> true [[_ _ false] | _] -> false [_ | Xs] -> (fj.hc-all-bad? Xs))
(define fj.hc-all-good? [] -> true [[_ _ true] | _] -> false [_ | Xs] -> (fj.hc-all-good? Xs))
(define fj.hc-resolved?
  [] _ -> true
  [O | Os] Obs ->
    (let S (fj.hc-observation (fj.hc-op-id O) Obs)
      (and (or (= S applied) (= S not-applied)) (fj.hc-resolved? Os Obs))))
(define fj.hc-count-triple?
  [R O S] -> (and (fj.hc-natural? R) (and (fj.hc-natural? O) (fj.hc-natural? S)))
  _ -> false)
(define fj.hc-natural?
  N -> (and (integer? N) (and (>= N 0) (<= N 32))))
(define fj.hc-final?
  [fj-final [fj-snapshot 0 W CA CB]] ->
    (and (fj.hc-world? W) (and (fj.hc-count-triple? CA) (fj.hc-count-triple? CB)))
  [fj-final W] -> (fj.hc-world? W)
  _ -> false)
(define fj.hc-result
  Final Ops Obs Leaves ->
    (if (fj.hc-final? Final)
      (fj.hc-classify (fj.hc-filter-final Final Leaves) (fj.hc-resolved? Ops Obs))
      [unknown missing-final-observation]))
(define fj.hc-classify
  [] _ -> [violation impossible-observation]
  L Resolved ->
    (if (fj.hc-all-bad? L) [violation bad-terminal]
      (if (fj.hc-all-good? L)
        (if Resolved [checked finite-history-consistency] [unknown unresolved-observation])
        [unknown mixed-terminal-outcomes])))
(define fj.hc-pred-lists?
  [] _ -> true
  [[fj-op I _ P _ _] | Os] Ids ->
    (and (fj.hc-unique? P)
      (and (fj.hc-subset? P Ids)
        (and (not (fj.hc-member? I P)) (fj.hc-pred-lists? Os Ids)))))
(define fj.hc-obs-ids
  [] -> []
  [[fj-effect Id _] | Os] -> [Id | (fj.hc-obs-ids Os)])
(define fj.hc-node-shapes?
  [] -> true
  [[fj-node _ _ _ _] | Ns] -> (fj.hc-node-shapes? Ns)
  _ -> false)
(define fj.hc-edge-shapes?
  [] -> true
  [[fj-edge _ _ _ B] | Es] ->
    (and (or (= B applied) (= B not-applied)) (fj.hc-edge-shapes? Es))
  _ -> false)
(define fj.hc-metadata?
  Ops Obs Nodes Edges ->
    (and (fj.hc-ops? Ops)
      (and (<= (length Ops) 32)
        (and (fj.hc-obs? Obs)
          (and (fj.hc-node-shapes? Nodes)
            (and (fj.hc-edge-shapes? Edges)
              (and (fj.hc-unique? (fj.hc-ids Ops))
                (and (fj.hc-pred-lists? Ops (fj.hc-ids Ops))
                  (and (fj.hc-unique? (fj.hc-obs-ids Obs))
                    (and (fj.hc-subset? (fj.hc-obs-ids Obs) (fj.hc-ids Ops))
                         (fj.hc-acyclic? Ops Ops)))))))))))
(define fj.check-history
  [fj-evidence 0 [fj-history 0 Ops Obs Final] [fj-dag 2 Nodes Edges 0]] ->
    (if (fj.hc-metadata? Ops Obs Nodes Edges)
      (if (and (<= (length Nodes) 512) (<= (length Edges) 100000))
        (if (and (fj.hc-unique? (fj.hc-node-ids Nodes)) (fj.hc-unique? Edges))
          (fj.hc-check-history-body Ops Obs Final Nodes Edges)
          [rejected duplicate-node-or-edge])
        [unknown history-certificate-budget])
      [rejected malformed-certificate])
  _ -> [rejected malformed-certificate])
(define fj.hc-check-history-body
  Ops Obs Final Nodes Edges -> (fj.hc-body-root [Ops Obs Final Nodes Edges]))
(define fj.hc-body-root
  [Ops Obs Final [[fj-node 0 W R false] | Ns] Edges] ->
    (if (= W (fj.initial))
      (if (= R (fj.hc-ids Ops))
        (if (fj.hc-world? W)
          (let All [[fj-node 0 W R false] | Ns]
            C (fj.hc-check-nodes All All Ops Obs Edges)
            (if (= C [ok])
              (let E (fj.hc-check-edges Edges All Ops Obs)
                (if (= E [ok])
                  (let Reach (fj.hc-reach [0] Edges [])
                    (if (fj.hc-all-reach? All Reach)
                      (fj.hc-result Final Ops Obs (fj.hc-leaves All))
                      [rejected unreachable-node]))
                  E))
              C))
          [rejected malformed-world])
        [rejected root-remaining])
      [rejected bad-root])
  _ -> [rejected bad-root])
