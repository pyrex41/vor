\\ R02 acceptance: finite inert proof trees, fixed rules, threaded node fuel.
(tc -)

(define vor.fol-root-inventory
  -> [vor-fol-root 0
       [hyp top pair fst snd intro apply inl inr cases exfalso gen inst
        witness unpack refl sym trans subst tree-induct]
       [finite-tree-algebra vor.tree vor.leaf vor.node]])

(define vor.fol-check
  Sig Vars Gamma P Evidence Fuel ->
    (trap-error
      (if (vor.fol-sequent? Sig Vars Gamma P)
        (if (and (vor.nat? Fuel) (<= Fuel 65535))
          (vor.fol-finish (vor.fol-derive Sig Vars Gamma P Evidence Fuel))
          [rejected invalid-proof-fuel])
        [rejected malformed-first-order-sequent])
      (/. E [unknown first-order-checker-error])))
(define vor.fol-finish
  [proved _] -> [accepted first-order-derivation]
  R -> R)
(define vor.fol-derive
  Sig V G P E Fuel -> (vor.fol-work Sig [[goal V G P E]] Fuel))

\\ Ordered depth-first work list: one shared node budget, no per-child reset.
\\ audit/rocq/Checker.v proves the generic scheduler metatheorems. Local rule
\\ validity and the Shen/model correspondence are separately tracked premises.
(define vor.fol-work
  _ [] Fuel -> [proved Fuel]
  _ [_ | _] 0 -> [unknown proof-fuel]
  Sig [[goal V G P E] | Rest] Fuel ->
    (vor.fol-work-expanded Sig Rest (- Fuel 1) (vor.fol-expand Sig V G P E))
  _ _ _ -> [rejected malformed-first-order-work])
(define vor.fol-work-expanded
  Sig Rest Fuel [premises Children] -> (vor.fol-work Sig (append Children Rest) Fuel)
  _ _ _ R -> R)

(define vor.fol-expand
  _ _ G P [hyp N] ->
    (if (and (vor.nat? N) (= (vor.fol-at G N) [found P]))
      [premises []] [rejected hypothesis])
  _ _ _ [top] [top] -> [premises []]
  _ V G [and P Q] [pair A B] ->
    [premises [[goal V G P A] [goal V G Q B]]]
  Sig V G P [fst Q E] ->
    (if (vor.fol-formula? Sig V Q)
      [premises [[goal V G [and P Q] E]]] [rejected malformed-annotation])
  Sig V G Q [snd P E] ->
    (if (vor.fol-formula? Sig V P)
      [premises [[goal V G [and P Q] E]]] [rejected malformed-annotation])
  _ V G [imp P Q] [intro E] -> [premises [[goal V [P | G] Q E]]]
  Sig V G Q [apply P A B] ->
    (if (vor.fol-formula? Sig V P)
      [premises [[goal V G [imp P Q] A] [goal V G P B]]]
      [rejected malformed-annotation])
  _ V G [or P _] [inl E] -> [premises [[goal V G P E]]]
  _ V G [or _ Q] [inr E] -> [premises [[goal V G Q E]]]
  Sig V G R [cases P Q E A B] ->
    (if (and (vor.fol-formula? Sig V P) (vor.fol-formula? Sig V Q))
      [premises [[goal V G [or P Q] E] [goal V [P | G] R A] [goal V [Q | G] R B]]]
      [rejected malformed-annotation])
  _ V G _ [exfalso E] -> [premises [[goal V G [bottom] E]]]
  _ V G [forall Sort P] [gen E] ->
    [premises [[goal [Sort | V] (vor.fol-shift-context G 1) P E]]]
  Sig V G P [inst Sort Body Term E] ->
    (if (vor.fol-instance? Sig V Sort Body Term P)
      [premises [[goal V G [forall Sort Body] E]]]
      [rejected invalid-instantiation])
  Sig V G [exists Sort Body] [witness Term E] ->
    (if (= (vor.fol-term-sort Sig V Term) [sort Sort])
      [premises [[goal V G (vor.fol-sub Body Term 0) E]]]
      [rejected wrong-witness-sort])
  Sig V G P [unpack Sort Body E Branch] ->
    (if (and (vor.member? Sort (vor.fol-sorts Sig))
             (vor.fol-formula? Sig [Sort | V] Body))
      [premises [[goal V G [exists Sort Body] E]
        [goal [Sort | V] [Body | (vor.fol-shift-context G 1)] (vor.fol-shift P 1 0) Branch]]]
      [rejected malformed-existential])
  _ _ _ [equal _ T T] [refl] -> [premises []]
  _ V G [equal Sort L R] [sym E] ->
    [premises [[goal V G [equal Sort R L] E]]]
  Sig V G [equal Sort L R] [trans Mid A B] ->
    (if (= (vor.fol-term-sort Sig V Mid) [sort Sort])
      [premises [[goal V G [equal Sort L Mid] A] [goal V G [equal Sort Mid R] B]]]
      [rejected wrong-middle-sort])
  Sig V G P [subst Sort Motive L R Eq Body] ->
    (if (and (vor.fol-instance? Sig V Sort Motive R P)
             (= (vor.fol-term-sort Sig V L) [sort Sort]))
      [premises [[goal V G [equal Sort L R] Eq]
                 [goal V G (vor.fol-sub Motive L 0) Body]]]
      [rejected invalid-equality-substitution])
  _ V G [forall vor.tree P] [tree-induct Base Step] ->
    (vor.fol-tree-goals V G P Base Step)
  Sig V G [forall Sort P] [data-induct Branches] ->
    (vor.algebra-induction Sig V G Sort P Branches)
  Sig V G [equal Sort L R] [inject C Index E] ->
    (vor.algebra-inject Sig V G Sort L R C Index E)
  Sig V G [bottom] [disjoint L R E] ->
    (vor.algebra-disjoint Sig V G L R E)
  _ _ _ _ _ -> [rejected invalid-first-order-proof])

(define vor.fol-instance?
  Sig V Sort Body Term P ->
    (and (vor.member? Sort (vor.fol-sorts Sig))
      (and (vor.fol-formula? Sig [Sort | V] Body)
        (and (= (vor.fol-term-sort Sig V Term) [sort Sort])
             (= P (vor.fol-sub Body Term 0))))))

(define vor.fol-tree-goals
  V G P Base Step ->
    (let Lifted (vor.fol-shift P 2 1)
      LeftIH (vor.fol-sub Lifted [v 1] 0)
      RightIH (vor.fol-sub Lifted [v 0] 0)
      Goal (vor.fol-sub Lifted [app vor.node [[v 1] [v 0]]] 0)
      [premises [[goal V G (vor.fol-sub P [app vor.leaf []] 0) Base]
        [goal [vor.tree vor.tree | V]
          [LeftIH RightIH | (vor.fol-shift-context G 2)] Goal Step]]]))

\\ System S checks the exact signature, scope, assumptions, and conclusion.
\\ This rule delegates to the same explicit checker; it is not independent.
(define vor.fol-code?
  Sig V G P Code -> (vor.fol-decoded? Sig V G P (vor.decode-claim-literal Code)))
(define vor.fol-decoded?
  Sig V G P [ok Evidence] ->
    (= (vor.fol-check Sig V G P Evidence 65535) [accepted first-order-derivation])
  _ _ _ _ _ -> false)
(datatype vor-first-order
  if (vor.fol-sequent? Sig V G P)
  if (vor.fol-code? Sig V G P E)
  ______________________________________________________
  E : (vor-fol-proves Sig V G P);)
(define vor.fol-typecheck
  Sig V G P E -> (vor.fol-typecheck-bounded Sig V G P E 65535))
(define vor.fol-typecheck-bounded
  Sig V G P E Fuel ->
    (trap-error
      (vor.fol-typecheck-result Sig V G P E (vor.fol-check Sig V G P E Fuel))
      (/. Error [unknown first-order-typechecker-error])))
(define vor.fol-typecheck-result
  Sig V G P E [accepted first-order-derivation] ->
    (if (vor.system-s? E [vor-fol-proves Sig V G P])
      [accepted first-order-typed-evidence] [rejected invalid-first-order-evidence])
  _ _ _ _ _ R -> R)
