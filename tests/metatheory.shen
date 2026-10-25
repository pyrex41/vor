(tc -)
\\ Test-only prior recursive scheduler, independent of the new work-list walk.
(define meta-test.rec-derive
  _ _ _ _ _ 0 -> [unknown proof-fuel]
  Sig V G P E Fuel -> (meta-test.rec-expanded Sig (vor.fol-expand Sig V G P E) (- Fuel 1)))
(define meta-test.rec-expanded
  Sig [premises Goals] Fuel -> (meta-test.rec-run Sig Goals Fuel)
  _ R _ -> R)
(define meta-test.rec-run
  _ [] Fuel -> [proved Fuel]
  Sig [[goal V G P E] | Goals] Fuel ->
    (meta-test.rec-next Sig Goals (meta-test.rec-derive Sig V G P E Fuel)))
(define meta-test.rec-next
  Sig Goals [proved Fuel] -> (meta-test.rec-run Sig Goals Fuel)
  _ _ R -> R)
(define meta-test.compare-case
  _ _ _ _ _ 21 -> done
  V G P E Sig Fuel ->
    (do (test.equal worklist-recursive-correspondence
      (vor.fol-derive Sig V G P E Fuel) (meta-test.rec-derive Sig V G P E Fuel))
      (meta-test.compare-case V G P E Sig (+ Fuel 1))))
(define meta-test.compare-cases
  [] -> done
  [[case _ V G P E _] | Cs] ->
    (do (meta-test.compare-case V G P E (fol-test.signature) 0) (meta-test.compare-cases Cs)))
(meta-test.compare-cases (value *fol-test-cases*))

(define meta-test.artifact
  -> (meta-test.compiled (vor.compile-program (admission-demo.program))))
(define meta-test.compiled [compiled A] -> A)
(test.equal compilation-valid
  (vor.check-compilation (admission-demo.program) (meta-test.artifact)) [accepted compilation])
(test.equal compiler-lexical-order
  (vor.compile-expression [bind [local 0] [primitive cons [[local 0] [local 1]]]])
  [[get 0] [enter] [get 0] [get 1] [join] [leave]])
(test.equal compiler-call-order
  (vor.compile-expression [invoke f [[local 0] [local 1]]]) [[get 0] [get 1] [call f 2]])
(test.equal compilation-no-host-code
  (hd (vor.check-expression-code [eval-kl [load "attack"]] [])) rejected)
(test.equal compilation-no-scope-loss
  (hd (vor.check-expression-code [bind [local 0] [local 0]] [[get 0] [enter] [get 0]])) rejected)
(test.equal compilation-no-wrong-scope
  (hd (vor.check-expression-code [bind [local 0] [local 0]] [[get 0] [enter] [get 1] [leave]])) rejected)
(test.equal compilation-no-extra-instruction
  (vor.check-expression-code [local 0] [[get 0] [push forged]]) [suffix [[push forged]]])
(test.equal compilation-no-reordered-arguments
  (hd (vor.check-expression-code [invoke f [[local 0] [local 1]]]
    [[get 1] [get 0] [call f 2]])) rejected)
(test.equal compilation-no-wrong-callee
  (hd (vor.check-expression-code [invoke f [[local 0]]] [[get 0] [call g 1]])) rejected)
(test.equal compilation-no-wrong-arity
  (hd (vor.check-expression-code [invoke f [[local 0]]] [[get 0] [call f 2]])) rejected)
(test.equal compilation-no-cons-swap
  (hd (vor.check-expression-code [primitive cons [[literal a] [literal b]]]
    [[push b] [push a] [join]])) rejected)
(test.equal compilation-no-identity-substitution
  (vor.check-compilation (admit-test.mutant [total.copy (admit-test.x)] [total.copy zero])
    (meta-test.artifact)) [rejected compilation-identity])
(define meta-test.replace-code
  A B -> (admit-test.replace (meta-test.artifact) A B))
(test.equal compilation-no-changed-function
  (hd (vor.check-compilation (admission-demo.program)
    (meta-test.replace-code [call total.copy 1] [call total.twice 1]))) rejected)
(test.equal compilation-no-missing-leave
  (hd (vor.check-compilation (admission-demo.program)
    (meta-test.replace-code [[leave]] []))) rejected)
(test.equal compilation-no-proof-flag
  (vor.check-compilation (admission-demo.program) true) [rejected compilation-identity])
(test.equal code-lexical-let
  (vor.code-run (admission-demo.program) [[get 0] [enter] [get 1] [leave]] [a b] [] [] 4)
  [code-result [a b] [a] []])
(test.equal code-argument-order
  (vor.code-pop 2 [second first rest] []) [arguments [first second] [rest]])
(test.equal code-empty-frame-rejected
  (hd (vor.code-run (admission-demo.program) [[leave]] [] [] [] 1)) rejected)
(test.equal code-dangling-local-rejected
  (vor.code-run (admission-demo.program) [[get 2]] [a] [] [] 1) [rejected code-local])
(test.equal code-exhaustion-unknown
  (vor.code-run (admission-demo.program) [[push a]] [] [] [] 0) [unknown code-fuel])
(test.equal compiled-composition
  (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.twice [[succ [succ zero]]] 2000)
  [compiled-value [succ [succ [succ [succ zero]]]]])
(test.equal compiled-append
  (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.append
    [[cell zero [cell [succ zero] nil]] [cell [succ [succ zero]] nil]] 2000)
  [compiled-value [cell zero [cell [succ zero] [cell [succ [succ zero]] nil]]]])
(test.equal compiled-zero-budget
  (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.copy [zero] 0)
  [unknown code-fuel])
(define meta-test.compiler-row
  _ 9 -> done
  A B -> (do (test.equal compiled-add-independent-reference
    (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.add
      [(data-test.peano A) (data-test.peano B)] 2000)
    [compiled-value (data-test.peano (+ A B))]) (meta-test.compiler-row A (+ B 1))))
(define meta-test.compiler-grid
  9 -> done
  A -> (do (meta-test.compiler-row A 0) (meta-test.compiler-grid (+ A 1))))
(meta-test.compiler-grid 0)
(test.equal compiled-accumulator-reversal
  (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.reverse
    [[cell zero [cell [succ zero] nil]] [cell [succ [succ zero]] nil]] 2000)
  [compiled-value [cell [succ zero] [cell zero [cell [succ [succ zero]] nil]]]])
(test.equal compiled-invalid-budget
  (vor.compiled-outcome (admission-demo.program) (meta-test.artifact) total.copy [zero] -1)
  [rejected invalid-code-fuel])
(define meta-test.compilation-claim
  -> [vor-claim 0 (test.root) [program (admission-demo.program)] []
    [[runtime trusted-image] [audit source-model-bridge-open]] constructor-stack-0
    [compiles (meta-test.artifact)] concrete-derivation])
(define meta-test.compilation-envelope
  -> [vor-evidence 0 (meta-test.compilation-claim) (meta-test.artifact)])
(test.equal compilation-bound-claim
  (vor.check-claim (test.root) (meta-test.compilation-claim) (meta-test.compilation-envelope) 1000)
  [checked (meta-test.compilation-claim) [accepted compilation]])
(test.equal compilation-bound-typed
  (vor.typecheck-claim (test.root) (meta-test.compilation-claim) (meta-test.compilation-envelope))
  [checked (meta-test.compilation-claim) [accepted typed-evidence]])
(test.equal compilation-bound-wire
  (vor.check-artifact (test.root) (meta-test.compilation-claim)
    (test.ok (vor.pack (meta-test.compilation-envelope) 1048576 256 65536)) 1048576 256 65536 1000)
  [checked (meta-test.compilation-claim) [accepted compilation]])
(test.equal compilation-proof-substitution
  (vor.check-claim (test.root) (meta-test.compilation-claim)
    [vor-evidence 0 (meta-test.compilation-claim) [accepted compilation]] 1000)
  [rejected compilation-evidence-mismatch])
(test.equal worklist-validates-generated-scope
  (vor.fol-work (fol-test.signature)
    [[goal [] [] [equal person [v 0] [v 0]] [refl]]] 10)
  [rejected malformed-first-order-work-sequent])
(test.equal worklist-zero-is-still-unknown
  (vor.fol-work (fol-test.signature)
    [[goal [] [] [equal person [v 0] [v 0]] [refl]]] 0)
  [unknown proof-fuel])
(test.equal native-lookup-large-index (vor.fol-at [a b c] 65535) missing)
(test.equal native-lookup-preserves-inert-payload
  (vor.fol-at [[load "never execute"] [false [a | b]] "text"] 1) [found [false [a | b]]])
