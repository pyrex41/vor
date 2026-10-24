\\ Trusted R04 rule expansion. Every branch is checked by the existing bounded
\\ first-order kernel. Constructor fields become fresh variables in field order.
(tc -)
(define vor.algebra-induction
  Sig V G S P Branches ->
    (vor.algebra-induction-data V G S P Branches (vor.algebra-data S Sig)))
(define vor.algebra-induction-data
  V G S P Branches [constructors Cs] -> (vor.algebra-branches V G S P Cs Branches)
  _ _ _ _ _ _ -> [rejected induction-sort])
(define vor.algebra-variables
  0 _ -> []
  N I -> [[v I] | (vor.algebra-variables (- N 1) (+ I 1))])
(define vor.algebra-hypotheses
  _ _ [] _ -> []
  S P [S | Ss] I -> [(vor.fol-sub P [v I] 0) | (vor.algebra-hypotheses S P Ss (+ I 1))]
  S P [_ | Ss] I -> (vor.algebra-hypotheses S P Ss (+ I 1)))
(define vor.algebra-branches
  _ _ _ _ [] [] -> [premises []]
  V G S P [[C Fields] | Cs] [[C E] | Es] ->
    (vor.algebra-branch-append
      (let N (length Fields)
        Lifted (vor.fol-shift P N 1)
        [goal (append Fields V)
          (append (vor.algebra-hypotheses S Lifted Fields 0) (vor.fol-shift-context G N))
          (vor.fol-sub Lifted [app C (vor.algebra-variables N 0)] 0) E])
      (vor.algebra-branches V G S P Cs Es))
  _ _ _ _ _ _ -> [rejected induction-coverage])
(define vor.algebra-branch-append
  Goal [premises Rest] -> [premises [Goal | Rest]]
  _ R -> R)

\\ Injection annotates the entire constructor argument vectors, preventing an
\\ unrelated equality from justifying a selected field equality.
(define vor.algebra-inject
  Sig V G S L R [C As Bs] I E ->
    (vor.algebra-inject-fields Sig V G S L R C As Bs I E (vor.algebra-constructor C Sig))
  _ _ _ _ _ _ _ _ _ -> [rejected injection-annotation])
(define vor.algebra-inject-fields
  Sig V G S L R C As Bs I E [function Fields Result] ->
    (if (and (vor.nat? I)
      (and (= (vor.fol-at Fields I) [found S])
        (and (= (vor.fol-at As I) [found L])
          (and (= (vor.fol-at Bs I) [found R])
            (and (vor.fol-arguments? Sig V As Fields) (vor.fol-arguments? Sig V Bs Fields))))))
      [premises [[goal V G [equal Result [app C As] [app C Bs]] E]]]
      [rejected injection-fields])
  _ _ _ _ _ _ _ _ _ _ _ _ -> [rejected injection-constructor])
(define vor.algebra-disjoint
  Sig V G [app C As] [app D Bs] E ->
    (vor.algebra-disjoint-fields Sig V G C As D Bs E
      (vor.algebra-constructor C Sig) (vor.algebra-constructor D Sig))
  _ _ _ _ _ _ -> [rejected disjoint-annotation])
(define vor.algebra-disjoint-fields
  Sig V G C As D Bs E [function Cs S] [function Ds S] ->
    (if (and (not (= C D))
      (and (vor.fol-arguments? Sig V As Cs) (vor.fol-arguments? Sig V Bs Ds)))
      [premises [[goal V G [equal S [app C As] [app D Bs]] E]]]
      [rejected disjoint-constructors])
  _ _ _ _ _ _ _ _ _ _ -> [rejected disjoint-sorts])
