\\ Partial observations retain ALL compatible successors; never pick one.
(tc -)
(define vor.observation?
  _ [] -> true
  Ns [[N true] | Fs] -> (and (vor.member? N Ns) (vor.observation? Ns Fs))
  Ns [[N false] | Fs] -> (and (vor.member? N Ns) (vor.observation? Ns Fs))
  _ _ -> false)

(define vor.matches?
  _ _ [] -> true
  Ns S [[N B] | Fs] ->
    (and (= B (vor.lookup N Ns S)) (vor.matches? Ns S Fs)))

(define vor.observed-targets
  _ [] _ _ -> []
  Ns [[step L T] | Es] L Fields ->
    (if (vor.matches? Ns T Fields)
        [T | (vor.observed-targets Ns Es L Fields)]
        (vor.observed-targets Ns Es L Fields))
  Ns [_ | Es] L Fields -> (vor.observed-targets Ns Es L Fields))

(define vor.union
  [] Ys -> Ys
  [X | Xs] Ys -> (vor.union Xs (if (vor.member? X Ys) Ys (append Ys [X]))))

(define vor.observe-all
  _ [] _ _ -> []
  M [S | Ss] L Fields ->
    (vor.union (vor.observed-targets (vor.vars M)
                 (vor.successors (vor.vars M) S (vor.rules M)) L Fields)
               (vor.observe-all M Ss L Fields)))

(define vor.observe
  M Belief Label Fields Bound ->
    (if (vor.model? M)
        (if (and (vor.states? (vor.vars M) Belief)
                 (and (not (= Belief [])) (vor.unique? Belief)))
            (if (vor.observation? (vor.vars M) Fields)
                (if (vor.unique? (vor.keys Fields))
                    (if (and (vor.nat? Bound) (> Bound 0))
                        (if (> (length Belief) Bound)
                            [unknown state-budget]
                            (vor.observe-result
                              (vor.observe-all M Belief Label Fields) Bound))
                        [rejected invalid-budget])
                    [rejected duplicate-observation-field])
                [rejected malformed-observation])
            [rejected invalid-belief-set])
        [rejected invalid-model]))

(define vor.observe-result
  [] _ -> [violation forbidden-observation]
  Ss Bound -> (if (> (length Ss) Bound)
                  [unknown state-budget]
                  [consistent Ss]))
