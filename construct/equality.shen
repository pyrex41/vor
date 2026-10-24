\\ Untrusted bounded equational proof producer. Its output consists solely of
\\ R02 equality/substitution/instantiation proof terms; no new inference rule.
(tc -)
(define vor.eq-strip
  [forall S P] Sorts -> (vor.eq-strip P [S | Sorts])
  [equal S L R] Sorts -> [equation Sorts S L R]
  _ _ -> missing)
(define vor.eq-match
  [v I] T N Bindings ->
    (vor.eq-bind I T Bindings) where (< I N)
  [v I] [v J] N Bindings -> (if (= J (- I N)) [matches Bindings] no-match)
  [app C Ps] [app C Ts] N Bindings -> (vor.eq-match-args Ps Ts N Bindings)
  _ _ _ _ -> no-match)
(define vor.eq-bind
  I T Bs -> (vor.eq-bind-at I T Bs 0))
(define vor.eq-bind-at
  I T [] J ->
    (if (= I J) [matches [[bound T]]] (vor.eq-bind-prefix (vor.eq-bind-at I T [] (+ J 1))))
  I T [[bound T] | Bs] I -> [matches [[bound T] | Bs]]
  I T [unbound | Bs] I -> [matches [[bound T] | Bs]]
  I T [_ | _] I -> no-match
  I T [B | Bs] J -> (vor.eq-bind-keep B (vor.eq-bind-at I T Bs (+ J 1))))
(define vor.eq-bind-prefix
  [matches Bs] -> [matches [unbound | Bs]]
  R -> R)
(define vor.eq-bind-keep
  B [matches Bs] -> [matches [B | Bs]]
  _ R -> R)
(define vor.eq-match-args
  [] [] _ Bs -> [matches Bs]
  [P | Ps] [T | Ts] N Bs -> (vor.eq-match-next Ps Ts N (vor.eq-match P T N Bs))
  _ _ _ _ -> no-match)
(define vor.eq-match-next
  Ps Ts N [matches Bs] -> (vor.eq-match-args Ps Ts N Bs)
  _ _ _ R -> R)
(define vor.eq-bound-terms
  [] -> [terms []]
  [[bound T] | Bs] -> (vor.eq-bound-next T (vor.eq-bound-terms Bs))
  _ -> missing)
(define vor.eq-bound-next
  T [terms Ts] -> [terms [T | Ts]]
  _ _ -> missing)
(define vor.eq-instantiate
  P [] -> P
  [forall _ P] [T | Ts] -> (vor.eq-instantiate (vor.fol-sub P T 0) Ts))
(define vor.eq-rewrite
  _ [] _ -> missing
  T [P | G] I ->
    (vor.eq-rewrite-next T G I (vor.eq-rule T P I (vor.eq-strip P []))))
(define vor.eq-rewrite-next
  _ _ _ [rewritten R E] -> [rewritten R E]
  T G I _ -> (vor.eq-rewrite T G (+ I 1)))
(define vor.eq-rule
  T P I [equation Ss _ L _] ->
    (vor.eq-rule-matched T P I (length Ss) (vor.eq-match L T (length Ss) []))
  _ _ _ _ -> missing)
(define vor.eq-rule-matched
  T P I N [matches Bs] ->
    (if (= N (length Bs)) (vor.eq-rule-bound T P I (vor.eq-bound-terms Bs)) missing)
  _ _ _ _ _ -> missing)
(define vor.eq-rule-bound
  T P I [terms Ts] ->
    (vor.eq-rule-result T (vor.eq-instantiate P (reverse Ts))
      (vor.proof-specialize P (reverse Ts) [hyp I]))
  _ _ _ _ -> missing)
(define vor.eq-rule-result
  T [equal _ T R] E -> (if (= T R) missing [rewritten R E])
  _ _ _ -> missing)

(define vor.eq-normal
  _ _ _ 0 -> [unknown equality-search-fuel]
  Sig G [v I] Fuel -> (vor.eq-root Sig G [v I] (- Fuel 1) [refl])
  Sig G [app C Ts] Fuel ->
    (vor.eq-normal-args Sig G C Ts (vor.eq-normals Sig G Ts (- Fuel 1)) (- Fuel 1)))
(define vor.eq-normals
  _ _ [] _ -> [normal-arguments [] []]
  Sig G [T | Ts] Fuel -> (vor.eq-normals-next (vor.eq-normal Sig G T Fuel) (vor.eq-normals Sig G Ts Fuel)))
(define vor.eq-normals-next
  [normal T E] [normal-arguments Ts Es] -> [normal-arguments [T | Ts] [E | Es]]
  [unknown R] _ -> [unknown R]
  _ R -> R)
(define vor.eq-normal-args
  Sig G C Ts [normal-arguments Rs Es] Fuel ->
    (vor.eq-root Sig G [app C Rs] Fuel
      (vor.eq-congruence Sig C Ts Rs Es))
  _ _ _ _ R _ -> R)
(define vor.eq-congruence
  Sig C Ts Rs Es ->
    (vor.eq-congruence-fields C Ts Rs Es (vor.fol-function C (vor.fol-functions Sig))))
(define vor.eq-congruence-fields
  C Ts Rs Es [function Ss Result] -> (vor.eq-cong-steps C Ts Rs Es Ss Result 0 [refl]))
(define vor.eq-cong-steps
  _ _ [] [] [] _ _ E -> E
  C Current [R | Rs] [A | As] [S | Ss] Result I E ->
    (let Next (vor.replace-at Current I R)
      L (vor.admit-at Current I)
      Step [subst S [equal Result
        [app C (vor.fol-shift-terms Current 1 0)]
        [app C (vor.replace-at (vor.fol-shift-terms Current 1 0) I [v 0])]] L R A [refl]]
      (vor.eq-cong-steps C Next Rs As Ss Result (+ I 1) [trans [app C Current] E Step])))
(define vor.eq-root
  Sig G T Fuel E -> (vor.eq-root-result Sig G T Fuel E (vor.eq-rewrite T G 0)))
\\ Chain annotates the intermediate *rewritten* term, not its normal form.
(define vor.eq-root-result
  Sig G T Fuel E [rewritten R A] -> (vor.eq-root-chain-at T R E A (vor.eq-normal Sig G R Fuel))
  _ _ T _ E missing -> [normal T E])
(define vor.eq-root-chain-at
  T Mid E A [normal R B] -> [normal R [trans T E [trans Mid A B]]]
  _ _ _ _ R -> R)
(define vor.prove-equality
  Sig G [equal _ L R] Fuel ->
    (vor.eq-close (vor.eq-normal Sig G L Fuel) (vor.eq-normal Sig G R Fuel)))
(define vor.eq-close
  [normal T A] [normal T B] -> [trans T A [sym B]]
  _ _ -> [search-failed])

(define vor.prove-induction
  Sig V G S P Fuel ->
    [data-induct (vor.prove-induction-data Sig V G S P Fuel (vor.algebra-data S Sig))])
(define vor.prove-induction-data
  Sig V G S P Fuel [constructors Cs] ->
    (vor.prove-induction-cases Sig V G S P Fuel Cs))
(define vor.prove-induction-cases
  _ _ _ _ _ _ [] -> []
  Sig V G S P Fuel [[C Fields] | Cs] ->
    (let Lifted (vor.fol-shift P (length Fields) 1)
      Gamma (append (vor.algebra-hypotheses S Lifted Fields 0)
                    (vor.fol-shift-context G (length Fields)))
      Target (vor.fol-sub Lifted [app C (vor.algebra-variables (length Fields) 0)] 0)
      [[C (vor.prove-equality Sig Gamma Target Fuel)] |
        (vor.prove-induction-cases Sig V G S P Fuel Cs)]))
