\\ VOR/0: closed Boolean transition semantics. Source is data, never eval'd.
\\ Internal functions require validated inputs. Public entry points validate.
(tc -)

(define vor.member?
  _ [] -> false
  X [Y | Ys] -> (or (= X Y) (vor.member? X Ys))
  _ _ -> false)

(define vor.proper?
  [] -> true
  [_ | Xs] -> (vor.proper? Xs)
  _ -> false)

(define vor.unique?
  [] -> true
  [X | Xs] -> (and (not (vor.member? X Xs)) (vor.unique? Xs))
  _ -> false)

(define vor.names?
  [] -> true
  [X | Xs] -> (and (symbol? X)
                    (and (not (= X true))
                         (and (not (= X false)) (vor.names? Xs))))
  _ -> false)

(define vor.nat?
  N -> (and (integer? N) (>= N 0)) where (number? N)
  _ -> false)

(define vor.state?
  [] [] -> true
  [_ | Ns] [true | Bs] -> (vor.state? Ns Bs)
  [_ | Ns] [false | Bs] -> (vor.state? Ns Bs)
  _ _ -> false)

(define vor.states?
  _ [] -> true
  Ns [S | Ss] -> (and (vor.state? Ns S) (vor.states? Ns Ss))
  _ _ -> false)

(define vor.expr?
  _ [lit true] -> true
  _ [lit false] -> true
  Ns [var N] -> (vor.member? N Ns)
  Ns [neg E] -> (vor.expr? Ns E)
  Ns [conj E F] -> (and (vor.expr? Ns E) (vor.expr? Ns F))
  Ns [disj E F] -> (and (vor.expr? Ns E) (vor.expr? Ns F))
  _ _ -> false)

(define vor.assignments?
  _ [] -> true
  Ns [[N E] | As] -> (and (vor.member? N Ns)
                          (and (vor.expr? Ns E)
                               (vor.assignments? Ns As)))
  _ _ -> false)

(define vor.keys
  [] -> []
  [[N _] | As] -> [N | (vor.keys As)])

(define vor.rules?
  _ [] -> true
  Ns [[rule Label Guard As] | Rs] ->
    (and (vor.names? [Label])
      (and (vor.expr? Ns Guard)
        (and (vor.assignments? Ns As)
          (and (vor.unique? (vor.keys As)) (vor.rules? Ns Rs)))))
  _ _ -> false)

(define vor.labels
  [] -> []
  [[rule L _ _] | Rs] -> [L | (vor.labels Rs)])

(define vor.model?
  [vor-model 0 Ns Initial Rules Invariant] ->
    (and (vor.names? Ns)
      (and (vor.unique? Ns)
        (and (vor.states? Ns Initial)
          (and (not (= Initial []))
            (and (vor.unique? Initial)
              (and (vor.rules? Ns Rules)
                (and (vor.unique? (vor.labels Rules))
                     (vor.expr? Ns Invariant))))))))
  _ -> false)

(define vor.vars [vor-model 0 Ns _ _ _] -> Ns)
(define vor.initial [vor-model 0 _ Is _ _] -> Is)
(define vor.rules [vor-model 0 _ _ Rs _] -> Rs)
(define vor.invariant [vor-model 0 _ _ _ I] -> I)

(define vor.lookup
  N [N | _] [B | _] -> B
  N [_ | Ns] [_ | Bs] -> (vor.lookup N Ns Bs))

(define vor.eval
  _ _ [lit B] -> B
  Ns S [var N] -> (vor.lookup N Ns S)
  Ns S [neg E] -> (not (vor.eval Ns S E))
  Ns S [conj E F] -> (and (vor.eval Ns S E) (vor.eval Ns S F))
  Ns S [disj E F] -> (or (vor.eval Ns S E) (vor.eval Ns S F)))

\\ All right-hand sides read the OLD state: assignment is simultaneous.
(define vor.assigned
  _ B [] _ _ -> B
  N _ [[N E] | _] Ns Old -> (vor.eval Ns Old E)
  N B [_ | As] Ns Old -> (vor.assigned N B As Ns Old))

(define vor.update
  [] [] _ _ _ -> []
  [N | Ns] [B | Bs] As All Old ->
    [(vor.assigned N B As All Old) | (vor.update Ns Bs As All Old)])

(define vor.successors
  Ns S [] -> []
  Ns S [[rule L G As] | Rs] ->
    (if (vor.eval Ns S G)
        [[step L (vor.update Ns S As Ns S)] | (vor.successors Ns S Rs)]
        (vor.successors Ns S Rs)))

(define vor.next
  M S -> (if (vor.model? M)
             (if (vor.state? (vor.vars M) S)
                 [ok (vor.successors (vor.vars M) S (vor.rules M))]
                 [rejected invalid-state])
             [rejected invalid-model]))

(define vor.safe?
  M S -> (vor.eval (vor.vars M) S (vor.invariant M)))

\\ A trace records the full initial state followed by labelled successors.
\\ No implicit stuttering, no invariant assumption about an arbitrary state.
(define vor.trace
  M T -> (if (vor.model? M)
             (vor.trace-start M T)
             [rejected invalid-model]))

(define vor.trace-start
  M [[initial S] | Steps] ->
    (if (and (vor.state? (vor.vars M) S) (vor.member? S (vor.initial M)))
        (if (vor.safe? M S)
            (vor.trace-rest M S Steps 1)
            [violation invariant 0 S])
        [rejected invalid-initial-state])
  _ _ -> [rejected invalid-trace])

(define vor.trace-rest
  _ _ [] N -> [accepted trace-prefix N]
  M S [[step L T] | Rest] N ->
    (if (vor.member? [step L T] (vor.successors (vor.vars M) S (vor.rules M)))
        (if (vor.safe? M T)
            (vor.trace-rest M T Rest (+ N 1))
            [violation invariant N T])
        [rejected illegal-step N])
  _ _ _ N -> [rejected malformed-trace N])
