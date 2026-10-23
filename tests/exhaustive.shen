\\ Independent oracle: enumerate the four Boolean states and compute closure
\\ as a bitset. Never call vor.eval/successors/explore in the oracle.
(tc -)
(define ref.state
  0 -> [false false]
  1 -> [true false]
  2 -> [false true]
  3 -> [true true])

(define ref.guard
  0 _ _ -> true
  1 X _ -> (not X)
  2 _ Y -> (not Y)
  3 X Y -> (not (and X Y)))

(define ref.guard-expr
  0 -> [lit true]
  1 -> [neg [var x]]
  2 -> [neg [var y]]
  3 -> [neg [conj [var x] [var y]]])

(define ref.mask-has?
  Mask Index -> (= 1 (mod (floor (/ Mask (expt 2 Index))) 2)))

(define ref.mask-add
  Mask Index -> (if (ref.mask-has? Mask Index) Mask (+ Mask (expt 2 Index))))

(define ref.targets
  Mask GX GY 4 -> Mask
  Mask GX GY I ->
    (let S (ref.state I)
      X (hd S)
      Y (hd (tl S))
      MX (if (and (ref.mask-has? Mask I) (ref.guard GX X Y))
             (ref.mask-add Mask (if Y 3 1)) Mask)
      MY (if (and (ref.mask-has? Mask I) (ref.guard GY X Y))
             (ref.mask-add MX (if X 3 2)) MX)
      (ref.targets MY GX GY (+ I 1))))

(define ref.closure
  GX GY Mask -> (let Next (ref.targets Mask GX GY 0)
                 (if (= Next Mask) Mask (ref.closure GX GY Next))))

(define ref.invariant
  0 -> [lit true]
  1 -> [neg [conj [var x] [var y]]]
  2 -> [neg [var x]]
  3 -> [neg [var y]])

(define ref.safe-mask?
  0 _ -> true
  1 Mask -> (not (ref.mask-has? Mask 3))
  2 Mask -> (and (not (ref.mask-has? Mask 1)) (not (ref.mask-has? Mask 3)))
  3 Mask -> (and (not (ref.mask-has? Mask 2)) (not (ref.mask-has? Mask 3))))

(define ref.model
  GX GY Inv ->
    [vor-model 0 [x y] [[false false]]
      [[rule enter-x (ref.guard-expr GX) [[x [lit true]]]]
       [rule enter-y (ref.guard-expr GY) [[y [lit true]]]]]
      (ref.invariant Inv)])

(define ref.check-result
  M true [certificate C] ->
    (test.equal exhaustive-certificate
      (hd (vor.check-certificate M C)) accepted)
  M false [counterexample T] ->
    (test.equal exhaustive-counterexample (hd (vor.trace M T)) violation)
  _ Expected Actual -> (error "oracle disagreement: expected safety ~A, got ~A" Expected Actual))

(define ref.loop
  4 _ _ -> done
  GX 4 _ -> (ref.loop (+ GX 1) 0 0)
  GX GY 4 -> (ref.loop GX (+ GY 1) 0)
  GX GY Inv ->
    (let M (ref.model GX GY Inv)
      (do (ref.check-result M (ref.safe-mask? Inv (ref.closure GX GY 1)) (vor.explore M 4))
          (ref.loop GX GY (+ Inv 1)))))

(ref.loop 0 0 0)
