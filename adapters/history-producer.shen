\\ Bounded causal-history producer. This is a candidate generator only: the
\\ acceptance checker must independently validate every node and edge.
(tc -)

(define fj.hp-member?
  _ [] -> false
  X [X | _] -> true
  X [_ | Xs] -> (fj.hp-member? X Xs)
  _ _ -> false)

(define fj.hp-remove
  _ [] -> []
  X [X | Xs] -> Xs
  X [Y | Xs] -> [Y | (fj.hp-remove X Xs)]
  _ _ -> [])

(define fj.hp-op-id [fj-op Id _ _ _ _] -> Id)
(define fj.hp-op-action [fj-op _ Action _ _ _] -> Action)
(define fj.hp-op-preds [fj-op _ _ Preds _ _] -> Preds)
(define fj.hp-op-effect [fj-op _ _ _ Effect _] -> Effect)
(define fj.hp-op-response [fj-op _ _ _ _ Response] -> Response)
(define fj.hp-op? [fj-op _ Action Preds Effect Response] ->
  (and (symbol? Action) (and (vor.proper? Preds)
    (and (or (= Effect applied) (or (= Effect not-applied) (= Effect unknown)))
      (or (= Response allow) (or (= Response deny) (= Response unknown))))))
  _ -> false)
(define fj.hp-ops?
  [] -> true
  [O | Os] -> (and (fj.hp-op? O) (fj.hp-ops? Os))
  _ -> false)
(define fj.hp-effect?
  [fj-effect _ Status] -> (or (= Status applied) (or (= Status not-applied) (= Status unknown)))
  _ -> false)
(define fj.hp-effects?
  [] -> true
  [E | Es] -> (and (fj.hp-effect? E) (fj.hp-effects? Es))
  _ -> false)
(define fj.hp-op-preds-valid?
  _ _ [] -> true
  Ops Id [P | Ps] -> (and (not (= P Id))
                         (and (fj.hp-member? P (fj.hp-ids Ops))
                              (fj.hp-op-preds-valid? Ops Id Ps)))
  _ _ _ -> false)
(define fj.hp-ops-valid?
  _ [] -> true
  Ops [[fj-op Id _ Preds _ _] | Os] ->
    (and (fj.hp-op-preds-valid? Ops Id Preds) (fj.hp-ops-valid? Ops Os))
  _ _ -> false)
(define fj.hp-observations-valid?
  _ [] -> true
  Ids [[fj-effect Id _] | Es] ->
    (and (fj.hp-member? Id Ids) (fj.hp-observations-valid? Ids Es))
  _ _ -> false)
(define fj.hp-ids
  [] -> []
  [[fj-op Id _ _ _ _] | Os] -> [Id | (fj.hp-ids Os)])
(define fj.hp-unique-ids?
  [] -> true
  [X | Xs] -> (and (not (fj.hp-member? X Xs)) (fj.hp-unique-ids? Xs)))
(define fj.hp-lookup-op
  _ [] -> missing
  Id [O | Os] -> (if (= Id (fj.hp-op-id O)) O (fj.hp-lookup-op Id Os)))
(define fj.hp-observation
  _ [] -> missing
  Id [[fj-effect Id Status] | _] -> Status
  Id [_ | Es] -> (fj.hp-observation Id Es))

(define fj.hp-eligible?
  [fj-op Id _ Preds _ _] Remaining ->
    (and (fj.hp-member? Id Remaining) (fj.hp-preds-free? Preds Remaining)))
(define fj.hp-preds-free?
  [] _ -> true
  [P | Ps] Remaining -> (and (not (fj.hp-member? P Remaining))
                             (fj.hp-preds-free? Ps Remaining)))
(define fj.hp-eligible
  [] _ -> []
  [O | Os] Remaining ->
    (if (fj.hp-eligible? O Remaining)
        [O | (fj.hp-eligible Os Remaining)]
        (fj.hp-eligible Os Remaining)))
(define fj.hp-remove-eligible-ids
  [] Remaining -> Remaining
  [O | Os] Remaining ->
    (fj.hp-remove-eligible-ids Os (fj.hp-remove (fj.hp-op-id O) Remaining)))
(define fj.hp-acyclic?
  Ops [] -> true
  Ops Remaining ->
    (let Ready (fj.hp-eligible Ops Remaining)
      (if (= Ready []) false
          (fj.hp-acyclic? Ops (fj.hp-remove-eligible-ids Ready Remaining)))))

(define fj.hp-branches
  Effect Obs Id -> (fj.hp-filter-branches (fj.hp-effect-branches Effect) (fj.hp-observation Id Obs)))
(define fj.hp-effect-branches
  applied -> [applied]
  not-applied -> [not-applied]
  unknown -> [applied not-applied]
  _ -> [])
(define fj.hp-filter-branches
  [] _ -> []
  [B | Bs] unknown -> [B | (fj.hp-filter-branches Bs unknown)]
  [B | Bs] missing -> [B | (fj.hp-filter-branches Bs missing)]
  [B | Bs] B -> [B | (fj.hp-filter-branches Bs B)]
  [_ | Bs] Obs -> (fj.hp-filter-branches Bs Obs))

(define fj.hp-key [World Remaining Bad] -> [World Remaining Bad])
(define fj.hp-find-node
  _ [] -> missing
  Key [[fj-node Id World Remaining Bad] | Ns] ->
    (if (= Key (fj.hp-key [World Remaining Bad])) Id
        (fj.hp-find-node Key Ns)))

\\ A model call is deliberately the only semantic operation here.
(define fj.hp-transition
  Action World Branch Response ->
    (let R (fj.next Action World)
      (fj.hp-transition-result R World Branch Response)))
(define fj.hp-transition-result
  [next allow W2] World applied Response ->
    [ok W2 (or (= Response deny) false)]
  [next deny _] World applied _ -> [ok World true]
  [next allow W2] World not-applied Response ->
    [ok World (or (= Response allow) (= Response deny))]
  [next deny _] World not-applied Response -> [ok World (= Response allow)]
  [unknown Reason] _ _ _ -> [unknown Reason]
  [rejected Reason] _ _ _ -> [unknown Reason]
  _ _ _ _ -> [unknown malformed-transition])

(define fj.hp-add-edge
  From To Op Branch Edges -> [[fj-edge From To Op Branch] | Edges])

\\ Expand one node. New nodes are returned in creation order and edges are
\\ accumulated in reverse order (reversed once at completion).
(define fj.hp-expand
  Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit ->
    (let World (fj.hp-node-world Node) Remaining (fj.hp-node-remaining Node)
         Bad (fj.hp-node-bad Node) Eligible (fj.hp-eligible Ops Remaining)
         (fj.hp-expand-ops Eligible Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit)))
(define fj.hp-node-world [fj-node _ W _ _] -> W)
(define fj.hp-node-remaining [fj-node _ _ R _] -> R)
(define fj.hp-node-bad [fj-node _ _ _ B] -> B)

(define fj.hp-expand-ops
  [] _ _ _ Nodes Queue Edges NextId EdgeCount _ _ -> [ok Nodes Queue Edges NextId EdgeCount]
  [O | Os] Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit ->
    (let Branches (fj.hp-branches (fj.hp-op-effect O) Obs (fj.hp-op-id O))
         R (fj.hp-expand-branches Branches O Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit)
      (fj.hp-expand-ops-result R Os Node Ops Obs NodeLimit Limit)))
(define fj.hp-expand-ops-result
  [ok Nodes Queue Edges NextId EdgeCount] Os Node Ops Obs NodeLimit Limit ->
    (fj.hp-expand-ops Os Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit)
  [unknown Reason] _ _ _ _ _ _ -> [unknown Reason])

\\ Carry the limit explicitly through branch expansion; this wrapper avoids
\\ host mutation and keeps transition/edge accounting identical.
(define fj.hp-expand-branches
  [] _ _ _ _ Nodes Queue Edges NextId EdgeCount _ _ -> [ok Nodes Queue Edges NextId EdgeCount]
  [Branch | Bs] O Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit ->
    (if (>= EdgeCount Limit) [unknown transition-budget]
      (let T (fj.hp-transition (fj.hp-op-action O) (fj.hp-node-world Node) Branch
                    (fj.hp-op-response O))
        (fj.hp-expand-transition T Branch O Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit Bs))))
(define fj.hp-expand-transition
  [unknown Reason] _ _ _ _ _ _ _ _ _ _ _ _ _ -> [unknown Reason]
  [ok World2 Bad2] Branch O Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit Limit Bs ->
    (let Remaining2 (fj.hp-remove (fj.hp-op-id O) (fj.hp-node-remaining Node))
         StickyBad (or (fj.hp-node-bad Node) Bad2)
         Key [World2 Remaining2 StickyBad]
         Found (fj.hp-find-node Key Nodes)
         From (fj.hp-node-id Node)
         (if (= Found missing)
             (if (>= NextId NodeLimit) [unknown node-budget]
               (let New [fj-node NextId World2 Remaining2 StickyBad]
                    NNodes (append Nodes [New]) NQueue (append Queue [New])
                 (fj.hp-expand-branches Bs O Node Ops Obs NNodes NQueue
                   (fj.hp-add-edge From NextId (fj.hp-op-id O) Branch Edges)
                   (+ NextId 1) (+ EdgeCount 1) NodeLimit Limit)))
             (fj.hp-expand-branches Bs O Node Ops Obs Nodes Queue
               (fj.hp-add-edge From Found (fj.hp-op-id O) Branch Edges)
               NextId (+ EdgeCount 1) NodeLimit Limit))))
(define fj.hp-node-id [fj-node Id _ _ _] -> Id)

(define fj.hp-run
  [] _ _ Nodes Edges NextId EdgeCount _ _ -> [produced Nodes Edges NextId EdgeCount]
  [Node | Queue] Ops Obs Nodes Edges NextId EdgeCount NodeLimit EdgeLimit ->
    (let R (fj.hp-expand Node Ops Obs Nodes Queue Edges NextId EdgeCount NodeLimit EdgeLimit)
      (fj.hp-run-result R Ops Obs NodeLimit EdgeLimit)))
(define fj.hp-run-result
  [unknown Reason] _ _ _ _ -> [unknown Reason]
  [ok Nodes Queue Edges NextId EdgeCount] Ops Obs NodeLimit EdgeLimit ->
    (fj.hp-run Queue Ops Obs Nodes Edges NextId EdgeCount NodeLimit EdgeLimit)
  _ _ _ _ _ -> [unknown internal-run])

(define fj.produce
  [fj-history 0 Ops Obs FinalFacts] NodeLimit EdgeLimit ->
    (if (fj.hp-budget-valid? NodeLimit EdgeLimit)
      (if (fj.hp-valid? Ops Obs FinalFacts)
          (fj.hp-start-result (fj.hp-run
            [[fj-node 0 (fj.initial) (fj.hp-ids Ops) false]] Ops Obs
            [[fj-node 0 (fj.initial) (fj.hp-ids Ops) false]] [] 1 0 NodeLimit EdgeLimit)
            [fj-history 0 Ops Obs FinalFacts])
          [rejected malformed-history])
      [rejected invalid-budget])
  _ _ _ -> [rejected malformed-history])
(define fj.hp-budget-valid?
  NodeLimit EdgeLimit ->
    (and (integer? NodeLimit) (and (>= NodeLimit 1) (and (<= NodeLimit 512)
      (and (integer? EdgeLimit) (and (>= EdgeLimit 1) (<= EdgeLimit 100000)))))))
(define fj.hp-valid?
  Ops Obs _ ->
    (and (fj.hp-ops? Ops)
      (and (<= (length Ops) 32)
        (and (fj.hp-unique-ids? (fj.hp-ids Ops))
          (and (fj.hp-ops-valid? Ops Ops)
            (and (fj.hp-acyclic? Ops (fj.hp-ids Ops))
              (and (fj.hp-effects? Obs)
                (and (fj.hp-unique-ids? (fj.hp-observation-ids Obs))
                  (fj.hp-observations-valid? (fj.hp-ids Ops) Obs)))))))))
(define fj.hp-start
  _ _ _ _ _ -> true)
(define fj.hp-observation-ids
  [] -> []
  [[fj-effect Id _] | Es] -> [Id | (fj.hp-observation-ids Es)])
(define fj.hp-start-result
  [produced Nodes Edges _ _] History ->
    [produced [fj-evidence 0 History [fj-dag 2 Nodes (reverse Edges) 0]]]
  [unknown Reason] _ -> [unknown Reason]
  _ _ -> [unknown producer-failure])
