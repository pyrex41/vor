\\ Independent constructive semantics: two ordered worlds, constant {0,1}
\\ domains, monotone unary predicate valuations, rigid functions/equality.
(tc -)
(define ref.kripke-truth
  [top] _ _ _ _ -> true
  [bottom] _ _ _ _ -> false
  [pred r [L R]] Env _ _ _ -> (= (ref.fol-term L Env) (ref.fol-term R Env))
  [pred Name Args] Env W Low High ->
    (ref.fol-truth [pred Name Args] Env (if (= W 0) Low High))
  [equal _ L R] Env _ _ _ -> (= (ref.fol-term L Env) (ref.fol-term R Env))
  [and P Q] Env W L H -> (and (ref.kripke-truth P Env W L H) (ref.kripke-truth Q Env W L H))
  [or P Q] Env W L H -> (or (ref.kripke-truth P Env W L H) (ref.kripke-truth Q Env W L H))
  [imp P Q] Env W L H ->
    (and (or (not (ref.kripke-truth P Env W L H)) (ref.kripke-truth Q Env W L H))
      (if (= W 0)
        (or (not (ref.kripke-truth P Env 1 L H)) (ref.kripke-truth Q Env 1 L H)) true))
  [forall _ P] Env W L H ->
    (and (and (ref.kripke-truth P [0 | Env] W L H) (ref.kripke-truth P [1 | Env] W L H))
      (if (= W 0)
        (and (ref.kripke-truth P [0 | Env] 1 L H) (ref.kripke-truth P [1 | Env] 1 L H)) true))
  [exists _ P] Env W L H ->
    (or (ref.kripke-truth P [0 | Env] W L H) (ref.kripke-truth P [1 | Env] W L H)))
(define ref.kripke-context
  [] _ _ _ _ -> true
  [P | Ps] E W L H -> (and (ref.kripke-truth P E W L H) (ref.kripke-context Ps E W L H)))
(define ref.kripke-monotone?
  _ _ 4 -> true
  L H I ->
    (and (or (not (ref.mask-has? L I)) (ref.mask-has? H I))
         (ref.kripke-monotone? L H (+ I 1))))
(define ref.kripke-envs
  _ _ [] _ _ -> done
  G P [Env | Envs] L H ->
    (do (test.equal kripke-world-zero
          (or (not (ref.kripke-context G Env 0 L H)) (ref.kripke-truth P Env 0 L H)) true)
      (do (test.equal kripke-world-one
            (or (not (ref.kripke-context G Env 1 L H)) (ref.kripke-truth P Env 1 L H)) true)
        (ref.kripke-envs G P Envs L H))))
(define ref.kripke-models
  _ _ _ 16 _ -> done
  G P Envs L 16 -> (ref.kripke-models G P Envs (+ L 1) 0)
  G P Envs L H ->
    (do (if (ref.kripke-monotone? L H 0) (ref.kripke-envs G P Envs L H) skipped)
        (ref.kripke-models G P Envs L (+ H 1))))
(define ref.kripke-cases
  [] -> done
  [[case _ V G P _ accepted] | Rest] ->
    (do (ref.kripke-models G P (ref.fol-envs (length V)) 0 0)
        (ref.kripke-cases Rest))
  [_ | Rest] -> (ref.kripke-cases Rest))
(ref.kripke-cases (value *fol-test-cases*))

\\ These formulas are classically valid but fail at the initial world.
(test.equal constructive-excluded-middle-countermodel
  (ref.kripke-truth [or (fol-test.p) [imp (fol-test.p) [bottom]]] [] 0 0 1) false)
(test.equal constructive-double-negation-countermodel
  (ref.kripke-truth [imp [imp [imp (fol-test.p) [bottom]] [bottom]] (fol-test.p)] [] 0 0 1) false)
(fol-test.case no-classical-axiom [] [] [or (fol-test.p) [imp (fol-test.p) [bottom]]] [excluded-middle] rejected)
(fol-test.case no-dne-axiom [] [] [imp [imp [imp (fol-test.p) [bottom]] [bottom]] (fol-test.p)] [double-negation] rejected)
