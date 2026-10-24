\\ A quantified theorem with explicit proof data, not search or test sampling.
(define fol-demo.signature
  -> [fol-signature 0 [value] [] [[p [value]] [q [value]]]])
(define fol-demo.p -> [pred p [[v 0]]])
(define fol-demo.q -> [pred q [[v 0]]])
(define fol-demo.theorem
  -> [imp [forall value [imp (fol-demo.p) (fol-demo.q)]]
       [imp [forall value (fol-demo.p)] [forall value (fol-demo.q)]]])
(define fol-demo.proof
  -> [intro [intro [gen [apply (fol-demo.p)
       [inst value [imp (fol-demo.p) (fol-demo.q)] [v 0] [hyp 1]]
       [inst value (fol-demo.p) [v 0] [hyp 0]]]]]])
(define fol-demo.check
  -> (vor.fol-check (fol-demo.signature) [] [] (fol-demo.theorem) (fol-demo.proof) 8))
(define fol-demo.typed
  -> (vor.fol-typecheck (fol-demo.signature) [] [] (fol-demo.theorem) (fol-demo.proof)))
