\\ The definition exists once as inert Shen source. No second native algorithm.
(define program-demo.source
  -> (let X (intern "X") Xs (intern "Xs") Ys (intern "Ys")
    [shen-source 0 [[define app.append [] Ys -> Ys
      [cons X Xs] Ys -> [cons X [app.append Xs Ys]]]]]))
(define program-demo.program
  -> (program-demo.normalized (vor.normalize (program-demo.source))))
(define program-demo.normalized
  [ok P] -> P
  R -> (error "demo source rejected: ~A" R))
(define program-demo.execution
  -> (vor.run (program-demo.program) app.append [[a b] [c d]] 1000))
(define program-demo.receipt
  [evaluated Outcome Evidence] ->
    [Outcome (vor.check-evaluation (program-demo.program) app.append [[a b] [c d]] Outcome Evidence 1000)]
  R -> R)
(define program-demo.run
  -> (program-demo.receipt (program-demo.execution)))
