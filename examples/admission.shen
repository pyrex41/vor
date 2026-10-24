\\ One definition per function. These inert reader-level ASTs are both the
\\ executable specification and the input to construction/admission.
(tc -)
(define admission-demo.source
  -> (let X (intern "X") Y (intern "Y") H (intern "H") T (intern "T")
    [shen-source 0
      [[define total.add zero Y -> Y
        [cons succ [cons X []]] Y -> [cons succ [cons [total.add X Y] []]]]
       [define total.copy zero -> zero
        [cons succ [cons X []]] -> [cons succ [cons [total.copy X] []]]]
       [define total.twice zero -> [total.add zero zero]
        [cons succ [cons X []]] ->
          [let Y [total.copy [cons succ [cons X []]]] [total.add Y Y]]]
       [define total.length nil -> zero
        [cons cell [cons H [cons T []]]] -> [cons succ [cons [total.length T] []]]]
       [define total.append nil Y -> Y
        [cons cell [cons H [cons T []]]] Y ->
          [cons cell [cons H [cons [total.append T Y] []]]]]
       [define total.reverse nil Y -> Y
        [cons cell [cons H [cons T []]]] Y ->
          [total.reverse T [cons cell [cons H [cons Y []]]]]]]]))
(define admission-demo.program -> (admission-demo.normalized (vor.normalize (admission-demo.source))))
(define admission-demo.normalized [ok P] -> P)
(define admission-demo.contracts
  -> [[contract total.add [natural natural] natural 0
        [imp [equal natural [v 2] [app zero []]] [equal natural [v 0] [v 1]]]]
      [contract total.copy [natural] natural 0 [equal natural [v 0] [v 1]]]
      [contract total.twice [natural] natural 0
        [equal natural [v 0] [app total.add [[v 1] [v 1]]]]]
      [contract total.length [nat-list] natural 0 [top]]
      [contract total.append [nat-list nat-list] nat-list 0
        [equal natural [app total.length [[v 0]]]
          [app total.add [[app total.length [[v 1]]] [app total.length [[v 2]]]]]]]
      [contract total.reverse [nat-list nat-list] nat-list 0
        [equal natural [app total.length [[v 0]]]
          [app total.add [[app total.length [[v 1]]] [app total.length [[v 2]]]]]]]])
(define admission-demo.signature
  -> [fol-signature 1 [] (vor.contract-functions (admission-demo.contracts)) [] (vor.standard-data)])
(define admission-demo.construction
  -> (vor.construct (admission-demo.program) (admission-demo.signature) (admission-demo.contracts)))
(define admission-demo.equations
  -> (admission-demo.equations-of
    (vor.construct-check (admission-demo.program) (admission-demo.signature)
      (admission-demo.contracts) (admission-demo.construction))))
(define admission-demo.equations-of [constructed Eqs] -> Eqs)

\\ total.add's post: equality substitution reduces arbitrary Y=zero to the
\\ induction theorem add(X,zero)=X. This proves every natural input, no sampling.
(define admission-demo.add-post
  -> [gen [gen [intro
       [trans [app total.add [[v 0] [app zero []]]]
         [subst natural
           [equal natural [app total.add [[v 1] [v 2]]] [app total.add [[v 1] [v 0]]]]
           [v 1] [app zero []] [hyp 0] [refl]]
         [inst natural (vor.arithmetic-right-zero-body total.add) [v 0]
           (vor.arithmetic-right-zero total.add 1 2)]]]]])
(define admission-demo.copy-post
  -> [data-induct
       [[zero [hyp 2]]
        [succ [trans [app succ [[app total.copy [[v 0]]]]]
          (vor.proof-specialize
            [forall natural [equal natural [app total.copy [[app succ [[v 0]]]]]
              [app succ [[app total.copy [[v 0]]]]]]]
            [[v 0]] [hyp 4])
          (vor.proof-cong natural succ [app total.copy [[v 0]]] [v 0] [hyp 0])]]]])
\\ The composed function uses copy's theorem, reconstructed as a proof in the
\\ same exact equation context rather than accepting a declared dependency flag.
(define admission-demo.twice-post
  -> [data-induct
       [[zero [hyp 4]]
        [succ
          [trans [app total.add [[app total.copy [[app succ [[v 0]]]]]
                                 [app total.copy [[app succ [[v 0]]]]]]]
            (vor.proof-specialize
              [forall natural [equal natural [app total.twice [[app succ [[v 0]]]]]
                [app total.add [[app total.copy [[app succ [[v 0]]]]]
                               [app total.copy [[app succ [[v 0]]]]]]]]]
              [[v 0]] [hyp 6])
            [subst natural
              [equal natural
                [app total.add [[app total.copy [[app succ [[v 1]]]]]
                               [app total.copy [[app succ [[v 1]]]]]]]
                [app total.add [[v 0] [v 0]]]]
              [app total.copy [[app succ [[v 0]]]]] [app succ [[v 0]]]
              [inst natural [equal natural [app total.copy [[v 0]]] [v 0]]
                [app succ [[v 0]]] (admission-demo.copy-post-shifted)] [refl]]]]]])
\\ An extra induction hypothesis precedes the equations in twice's step.
(define admission-demo.copy-post-shifted
  -> [data-induct
       [[zero [hyp 3]]
        [succ [trans [app succ [[app total.copy [[v 0]]]]]
          (vor.proof-specialize
            [forall natural [equal natural [app total.copy [[app succ [[v 0]]]]]
              [app succ [[app total.copy [[v 0]]]]]]]
            [[v 0]] [hyp 5])
          (vor.proof-cong natural succ [app total.copy [[v 0]]] [v 0] [hyp 0])]]]])
(define admission-demo.posts
  -> [[post total.add (admission-demo.add-post)]
      [post total.copy (admission-demo.copy-post)]
      [post total.twice (admission-demo.twice-post)]
      [post total.length [gen [top]]]
      [post total.append (admission-demo.append-post)]
      [post total.reverse (admission-demo.reverse-post)]])
(define admission-demo.evidence
  -> [vor-admission 0 (admission-demo.program) (admission-demo.signature)
       (admission-demo.contracts) (admission-demo.construction) (admission-demo.posts)])
(define admission-demo.check
  -> (vor.admit (admission-demo.program) (admission-demo.signature)
       (admission-demo.contracts) (admission-demo.evidence) 2000))

(define admission-demo.append-body
  -> [equal natural [app total.length [[app total.append [[v 0] [v 1]]]]]
       [app total.add [[app total.length [[v 0]]] [app total.length [[v 1]]]]]])
(define admission-demo.append-post
  -> [gen (vor.prove-induction (admission-demo.signature) [nat-list]
       (admission-demo.equations) nat-list (admission-demo.append-body) 100)])
(define admission-demo.append-right-nil
  -> (vor.prove-induction (admission-demo.signature) [] (admission-demo.equations)
       nat-list [equal nat-list [app total.append [[v 0] [app nil []]]] [v 0]] 100))
(define admission-demo.associativity
  -> [gen [gen
       (vor.prove-induction (admission-demo.signature) [natural natural]
         (admission-demo.equations) natural
         [equal natural [app total.add [[app total.add [[v 0] [v 1]]] [v 2]]]
           [app total.add [[v 0] [app total.add [[v 1] [v 2]]]]]] 100)]])

(define admission-demo.right-succ
  -> [forall natural [forall natural
    [equal natural [app total.add [[v 0] [app succ [[v 1]]]]]
      [app succ [[app total.add [[v 0] [v 1]]]]]]]])
(define admission-demo.right-succ-proof
  -> [gen (vor.prove-induction (admission-demo.signature) [natural]
    (admission-demo.equations) natural
    [equal natural [app total.add [[v 0] [app succ [[v 1]]]]]
      [app succ [[app total.add [[v 0] [v 1]]]]]] 100)])
(define admission-demo.reverse-motive
  -> [forall nat-list
    [equal natural [app total.length [[app total.reverse [[v 1] [v 0]]]]]
      [app total.add [[app total.length [[v 1]]] [app total.length [[v 0]]]]]]])
(define admission-demo.reverse-strong
  -> (vor.prove-induction (admission-demo.signature) []
       [(admission-demo.right-succ) | (admission-demo.equations)]
       nat-list (admission-demo.reverse-motive) 100))
(define admission-demo.reverse-post
  -> [apply (admission-demo.right-succ)
       [intro [gen [gen
         (vor.proof-specialize [forall nat-list (admission-demo.reverse-motive)]
           [[v 0] [v 1]] (admission-demo.reverse-strong))]]]
       (admission-demo.right-succ-proof)])
