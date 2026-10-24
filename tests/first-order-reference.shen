\\ Independent finite semantics. Never call the proof checker, term typer,
\\ shift, or substitution to interpret a formula. Both sorts use {0,1}.
\\ Tree quotient: leaf=0, node(l,r)=(l+r+1) mod 2, generated from leaf.
(tc -)
(define ref.fol-nth
  [X | _] 0 -> X
  [_ | Xs] N -> (ref.fol-nth Xs (- N 1)))
(define ref.fol-term
  [v N] Env -> (ref.fol-nth Env N)
  [app a []] _ -> 0
  [app b []] _ -> 1
  [app z []] _ -> 0
  [app f [T]] Env -> (- 1 (ref.fol-term T Env))
  [app vor.leaf []] _ -> 0
  [app vor.node [L R]] Env -> (mod (+ 1 (+ (ref.fol-term L Env) (ref.fol-term R Env))) 2))
(define ref.fol-truth
  [top] _ _ -> true
  [bottom] _ _ -> false
  [pred p [T]] Env M -> (ref.mask-has? M (ref.fol-term T Env))
  [pred q [T]] Env M -> (ref.mask-has? M (+ 2 (ref.fol-term T Env)))
  [pred r [L R]] Env M ->
    (ref.mask-has? M (+ 4 (+ (* 2 (ref.fol-term L Env)) (ref.fol-term R Env))))
  [pred tree-p [T]] Env M -> (ref.mask-has? M (ref.fol-term T Env))
  [pred flag []] _ M -> (ref.mask-has? M 0)
  [equal _ L R] Env _ -> (= (ref.fol-term L Env) (ref.fol-term R Env))
  [and P Q] Env M -> (and (ref.fol-truth P Env M) (ref.fol-truth Q Env M))
  [or P Q] Env M -> (or (ref.fol-truth P Env M) (ref.fol-truth Q Env M))
  [imp P Q] Env M -> (or (not (ref.fol-truth P Env M)) (ref.fol-truth Q Env M))
  [forall _ P] Env M -> (and (ref.fol-truth P [0 | Env] M) (ref.fol-truth P [1 | Env] M))
  [exists _ P] Env M -> (or (ref.fol-truth P [0 | Env] M) (ref.fol-truth P [1 | Env] M)))
(define ref.fol-context
  [] _ _ -> true
  [P | Ps] Env M -> (and (ref.fol-truth P Env M) (ref.fol-context Ps Env M)))
(define ref.fol-envs
  0 -> [[]]
  N -> (ref.fol-extend (ref.fol-envs (- N 1))))
(define ref.fol-extend
  [] -> []
  [E | Es] -> [[0 | E] [1 | E] | (ref.fol-extend Es)])
(define ref.fol-environments
  _ _ [] _ -> done
  G P [Env | Envs] M ->
    (do (test.equal finite-model-soundness
          (or (not (ref.fol-context G Env M)) (ref.fol-truth P Env M)) true)
        (ref.fol-environments G P Envs M)))
(define ref.fol-cases
  [] -> done
  [[case _ V G P _ accepted] | Rest] ->
    (do (ref.fol-check-models G P (ref.fol-envs (length V)) 0)
        (ref.fol-cases Rest))
  [_ | Rest] -> (ref.fol-cases Rest))
(define ref.fol-check-models
  _ _ _ 256 -> done
  G P Envs M -> (do (ref.fol-environments G P Envs M)
                   (ref.fol-check-models G P Envs (+ M 1))))
(ref.fol-cases (value *fol-test-cases*))

\\ Independently evaluate the semantic substitution and weakening equations.
(define ref.fol-bodies
  -> [[pred r [[v 0] [v 1]]]
      [equal person [app f [[v 0]]] [v 2]]
      [forall person [pred r [[v 1] [v 0]]]]
      [exists person [pred r [[v 0] [v 2]]]]
      [forall person [exists person [pred r [[v 2] [v 3]]]]]
      [imp [pred p [[v 0]]] [forall person [pred q [[v 1]]]]]])
(define ref.fol-terms
  -> [[app a []] [app b []] [v 0] [v 1] [app f [[v 0]]]])
(define ref.fol-substitution-check
  _ _ _ _ 256 -> done
  Body Term Instance Env M ->
    (do (test.equal semantic-substitution
          (ref.fol-truth Instance Env M)
          (ref.fol-truth Body [(ref.fol-term Term Env) | Env] M))
      (do (test.equal semantic-weakening
              (ref.fol-truth (vor.fol-shift Body 1 0) [1 (ref.fol-term Term Env) | Env] M)
              (ref.fol-truth Body [(ref.fol-term Term Env) | Env] M))
          (ref.fol-substitution-check Body Term Instance Env (+ M 1)))))
(define ref.fol-substitution-envs
  _ _ _ [] -> done
  Body Term Instance [Env | Rest] ->
    (do (ref.fol-substitution-check Body Term Instance Env 0)
        (ref.fol-substitution-envs Body Term Instance Rest)))
(define ref.fol-substitution-terms
  _ [] -> done
  Body [T | Ts] ->
    (let Instance (test.ok (vor.fol-instantiate (fol-test.signature) [person person] person Body T))
      (do (test.equal substitution-scope
            (vor.fol-formula? (fol-test.signature) [person person] Instance) true)
        (do (ref.fol-substitution-envs Body T Instance (ref.fol-envs 2))
            (ref.fol-substitution-terms Body Ts)))))
(define ref.fol-substitution-bodies
  [] -> done
  [Body | Bs] ->
    (do (ref.fol-substitution-terms Body (ref.fol-terms))
        (ref.fol-substitution-bodies Bs)))
(ref.fol-substitution-bodies (ref.fol-bodies))
