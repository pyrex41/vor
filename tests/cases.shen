(tc -)
(load "examples/scoping.shen")

(define cases-test.id-of
  1 -> id.one
  N -> [id.x0 (cases-test.id-of (/ N 2))] where (integer? (/ N 2))
  N -> [id.x1 (cases-test.id-of (/ (- N 1) 2))])
(define cases-test.table
  -> [projects.cons [project-row.mk [project (cases-test.id-of 7)] [company (cases-test.id-of 3)] no]
       [projects.cons [project-row.mk [project (cases-test.id-of 9)] [company (cases-test.id-of 4)] no]
         projects.nil]])
(define cases-test.run
  P Name Args ->
    (let Sig (scoping.signature) Cs (scoping.contracts)
      (cases-test.value (vor.run-admitted P Sig Cs
        [vor-admission 0 P Sig Cs (vor.construct P Sig Cs) (vor.derive-top-posts Cs)]
        Name Args 4000 20000))))
(define cases-test.value [executed-admitted [value V] _] -> V  R -> R)
(define cases-test.find
  P C Pr -> (cases-test.run P projects.find
              [(cases-test.table) [company (cases-test.id-of C)] [project (cases-test.id-of Pr)]]))

(set *cases-p* (scoping.program))
(set *cases-sig* (scoping.signature))
(set *cases-eqs* (scoping.equations-of (value *cases-p*) (value *cases-sig*) (scoping.contracts)))
(set *cases-y* (scoping.always-yes))
(set *cases-yeqs* (scoping.equations-of (value *cases-y*) (value *cases-sig*) (scoping.contracts)))
(set *cases-m* (scoping.no-company-check))
(set *cases-meqs* (scoping.equations-of (value *cases-m*) (value *cases-sig*) (scoping.contracts)))

\\ The producer adds no rule: both kernel inventories are unchanged.
(test.equal cases-fol-root-unchanged (hd (tl (vor.fol-root-inventory))) 0)
(test.equal cases-construction-root-unchanged (hd (tl (vor.construction-root-inventory))) 2)

\\ Gap 1: identifier equality soundness, by induction on X then Y, intro,
\\ disjoint for the six mismatched cases and the IH for the two matching ones.
(test.equal cases-id-eq-sound
  (scoping.theorem (value *cases-p*) (scoping.sound id id.eq)
    (scoping.sound-proof (value *cases-sig*) (value *cases-eqs*)))
  [accepted constructed-theorem])
(test.equal cases-id-eq-sound-fuel
  (vor.check-constructed-theorem (value *cases-p*) (value *cases-sig*) (scoping.contracts)
    (vor.construct (value *cases-p*) (value *cases-sig*) (scoping.contracts))
    (scoping.sound id id.eq) (scoping.sound-proof (value *cases-sig*) (value *cases-eqs*)) 40)
  [unknown proof-fuel])
(test.equal cases-scope-without-lemmas
  (scoping.theorem (value *cases-p*) (scoping.scope)
    (scoping.scope-proof (value *cases-sig*) (value *cases-eqs*)))
  [accepted constructed-theorem])
(test.equal cases-only-company
  (scoping.theorem (value *cases-p*) (scoping.only-company)
    (scoping.only-company-proof (value *cases-sig*) (value *cases-eqs*)))
  [accepted constructed-theorem])

\\ Replayed proofs cite definition equations that the mutant no longer has,
\\ so the kernel rejects the hypothesis step.
\\ Negative control: an always-yes id.eq is total and reflexive, but it leaks
\\ another company's row; soundness and only-company must both fail, both for
\\ the producer and when the accepted proof terms are replayed against it.
(test.equal cases-always-yes-admits
  (vor.admit (value *cases-y*) (value *cases-sig*) (scoping.contracts)
    [vor-admission 0 (value *cases-y*) (value *cases-sig*) (scoping.contracts)
      (vor.construct (value *cases-y*) (value *cases-sig*) (scoping.contracts))
      (vor.derive-top-posts (scoping.contracts))] 4000)
  [accepted total-admission])
\\ Asked for company 4, project 9, the mutant returns company 3's row.
(test.equal cases-always-yes-leaks (cases-test.find (value *cases-y*) 4 9)
  [project-row.some [project-row.mk [project (cases-test.id-of 7)] [company (cases-test.id-of 3)] no]])
(test.equal cases-real-same-company (cases-test.find (value *cases-p*) 4 9)
  [project-row.some [project-row.mk [project (cases-test.id-of 9)] [company (cases-test.id-of 4)] no]])
(test.equal cases-real-does-not-leak (cases-test.find (value *cases-p*) 3 9) project-row.none)
(test.equal cases-always-yes-unsound
  (scoping.theorem (value *cases-y*) (scoping.sound id id.eq)
    (scoping.sound-proof (value *cases-sig*) (value *cases-yeqs*)))
  [rejected invalid-first-order-proof])
(test.equal cases-always-yes-replayed-proof
  (scoping.theorem (value *cases-y*) (scoping.sound id id.eq)
    (scoping.sound-proof (value *cases-sig*) (value *cases-eqs*)))
  [rejected hypothesis])
(test.equal cases-always-yes-only-company
  (scoping.theorem (value *cases-y*) (scoping.only-company)
    (scoping.only-company-proof (value *cases-sig*) (value *cases-yeqs*)))
  [rejected invalid-first-order-proof])
(test.equal cases-always-yes-only-company-replayed
  (scoping.theorem (value *cases-y*) (scoping.only-company)
    (scoping.only-company-proof (value *cases-sig*) (value *cases-eqs*)))
  [rejected hypothesis])
(test.equal cases-no-check-leaks (cases-test.find (value *cases-m*) 3 9)
  [project-row.some [project-row.mk [project (cases-test.id-of 9)] [company (cases-test.id-of 4)] no]])
(test.equal cases-no-check-scope
  (scoping.theorem (value *cases-m*) (scoping.scope)
    (scoping.scope-proof (value *cases-sig*) (value *cases-meqs*)))
  [rejected invalid-first-order-proof])
(test.equal cases-no-check-scope-replayed
  (scoping.theorem (value *cases-m*) (scoping.scope)
    (scoping.scope-proof (value *cases-sig*) (value *cases-eqs*)))
  [rejected hypothesis])
(test.equal cases-no-check-only-company
  (scoping.theorem (value *cases-m*) (scoping.only-company)
    (scoping.only-company-proof (value *cases-sig*) (value *cases-meqs*)))
  [rejected invalid-first-order-proof])

\\ Gap 2: conditional theorems and conditional contract posts.
(test.equal cases-conditional
  (scoping.theorem (value *cases-p*) (scoping.conditional [app project-row.some [[v 0]]])
    (vor.prove-script (value *cases-sig*) [] (value *cases-eqs*)
      (scoping.conditional [app project-row.some [[v 0]]]) [] 200))
  [accepted constructed-theorem])
(test.equal cases-conditional-forged
  (scoping.theorem (value *cases-p*) (scoping.conditional [app project-row.none []])
    (vor.prove-script (value *cases-sig*) [] (value *cases-eqs*)
      (scoping.conditional [app project-row.none []]) [] 200))
  [rejected invalid-first-order-proof])
(test.equal cases-conditional-post
  (scoping.admit-with (value *cases-p*) (scoping.pick-contracts (scoping.pick-post-good)))
  [accepted total-admission])
(test.equal cases-conditional-post-wrong
  (scoping.admit-with (value *cases-p*) (scoping.pick-contracts (scoping.pick-post-wrong)))
  [rejected invalid-first-order-proof])
(test.equal cases-conditional-post-swapped-pick
  (scoping.admit-with
    (scoping.program-of (scoping.replace-definition truth.pick
      "(define truth.pick yes A B -> B no A B -> A)" (scoping.source)))
    (scoping.pick-contracts (scoping.pick-post-good)))
  [rejected invalid-first-order-proof])
\\ A false generic statement (fails for J = no) stays unproved.
(test.equal cases-false-theorem-rejected
  (scoping.theorem (value *cases-p*)
    [forall truth [equal truth [app truth.pick [[v 0] [app yes []] [app no []]]] [app yes []]]]
    (vor.prove-script (value *cases-sig*) [] (value *cases-eqs*)
      [forall truth [equal truth [app truth.pick [[v 0] [app yes []] [app no []]]] [app yes []]]] [] 200))
  [rejected invalid-first-order-proof])

\\ Derived structural equality: generated ordinary source, admitted like
\\ hand-written source; every reflexivity and soundness lemma is rechecked.
(set *cases-derived* (scoping.derived-parts (scoping.derived)))
(set *cases-dp* (scoping.derived-program (hd (value *cases-derived*))))
(set *cases-dcs* (nth 2 (value *cases-derived*)))
(set *cases-dls* (nth 3 (value *cases-derived*)))
(test.equal cases-derived-count (length (value *cases-dls*)) 14)
(test.equal cases-derived-admit (scoping.derived-admit (value *cases-dp*) (value *cases-dcs*))
  [accepted total-admission])
(test.equal cases-derived-lemmas
  (map (/. K (scoping.derived-lemma (value *cases-dp*) (value *cases-dcs*) (value *cases-dls*) K))
    (scoping.range 0 14))
  (map (/. K [accepted constructed-theorem]) (scoping.range 0 14)))
(define cases-test.derived-run
  P Cs A B ->
    (let Sig (scoping.derived-signature Cs)
      (cases-test.value (vor.run-admitted P Sig Cs
        [vor-admission 0 P Sig Cs (vor.construct P Sig Cs) (vor.derive-top-posts Cs)]
        derive.eq.id [(cases-test.id-of A) (cases-test.id-of B)] 4000 20000))))
(test.equal cases-derived-run-equal
  (cases-test.derived-run (value *cases-dp*) (value *cases-dcs*) 48213 48213) yes)
(test.equal cases-derived-run-distinct
  (cases-test.derived-run (value *cases-dp*) (value *cases-dcs*) 48213 48212) no)
\\ Tampered generated equality: soundness of id (lemma 3) must fail.
(set *cases-dy* (scoping.program-of (scoping.replace-definition derive.eq.id
  "(define derive.eq.id id.one Other -> yes [id.x0 X1] Other -> yes [id.x1 X1] Other -> yes)"
  [shen-source 0 (hd (value *cases-derived*))])))
(test.equal cases-derived-tampered-refl
  (scoping.derived-lemma (value *cases-dy*) (value *cases-dcs*) (value *cases-dls*) 2)
  [accepted constructed-theorem])
(test.equal cases-derived-tampered-sound
  (scoping.derived-lemma (value *cases-dy*) (value *cases-dcs*) (value *cases-dls*) 3)
  [rejected invalid-first-order-proof])
(test.equal cases-derived-bad-truth
  (vor.derive-eq (scoping.data) [id id.one id.x0] [id]) [rejected derived-eq-truth])
(test.equal cases-derived-bad-order
  (vor.derive-eq (scoping.data) [truth yes no] [truth company-id id]) [rejected [derived-eq-order company-id]])
