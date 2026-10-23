\\ Executable planning contract. These are REQUIRED evidence kinds, not results.
\\ Registry validation never proves an application theorem or completes a wave.
(tc -)

(define vor.roadmap
  -> [[stage r00 []
        [[goal r00-reproduce test] [goal r00-kernel-conformance test]
         [goal r00-finite-baseline finite-proof]]]
      [stage r01 [r00]
        [[goal r01-identity generic-proof] [goal r01-assumptions generic-proof]
         [goal r01-substitution-attacks test]]]
      [stage r02 [r01]
        [[goal r02-root-inventory audit] [goal r02-logic-formation audit]
         [goal r02-rule-corpus concrete-derivation]]]
      [stage r03 [r02]
        [[goal r03-normalization generic-proof] [goal r03-evaluation generic-proof]
         [goal r03-determinism generic-proof]]]
      [stage r04 [r02 r03]
        [[goal r04-induction generic-proof] [goal r04-arithmetic generic-proof]
         [goal r04-boolean-embedding generic-proof]]]
      [stage r05 [r01 r03 r04]
        [[goal r05-construction generic-proof] [goal r05-totality generic-proof]
         [goal r05-admission generic-proof]]]
      [stage r06 [r05]
        [[goal r06-transfer-contract generic-proof] [goal r06-execution concrete-derivation]
         [goal r06-mutant-rejection test]]]
      [stage r07 [r05 r06]
        [[goal r07-reachable-safety generic-proof] [goal r07-machine-construction generic-proof]]]
      [stage r08 [r07]
        [[goal r08-effect-closure generic-proof] [goal r08-uncertainty generic-proof]
         [goal r08-retry-reconcile generic-proof]]]
      [stage r09 [r07 r08]
        [[goal r09-interference generic-proof] [goal r09-resource-policy generic-proof]
         [goal r09-progress generic-proof]]]
      [stage r10 [r07 r08]
        [[goal r10-finite-acceptance generic-proof] [goal r10-observation-adequacy generic-proof]
         [goal r10-minimization generic-proof]]]
      [stage r11 [r04 r05]
        [[goal r11-translation generic-proof] [goal r11-reconstruction generic-proof]
         [goal r11-reconstructed-example concrete-derivation]]]
      [stage r12 [r01 r05 r07 r08 r10 r11]
        [[goal r12-discharge-policy generic-proof] [goal r12-agent-repair concrete-derivation]
         [goal r12-report-binding generic-proof]]]
      [stage r13 [r08 r10 r12]
        [[goal r13-adapter-mapping generic-proof] [goal r13-real-counterexample trace-check]
         [goal r13-replay-shrink test]]]
      [stage r14 [r08 r09 r13]
        [[goal r14-simulation generic-proof] [goal r14-concrete-assumptions audit]
         [goal r14-recovery generic-proof]]]
      [stage r15 [r05 r12 r14]
        [[goal r15-transformation generic-proof] [goal r15-fresh-image test]
         [goal r15-artifact-binding generic-proof]]]
      [stage r16 [r02 r04 r05 r07 r08 r10 r12 r15]
        [[goal r16-kernel-soundness generic-proof] [goal r16-checker-totality generic-proof]
         [goal r16-public-correspondence generic-proof] [goal r16-bootstrap-roots audit]]]
      [stage r17 [r06 r07 r09 r11 r12 r13 r14 r15 r16]
        [[goal r17-release-replay concrete-derivation] [goal r17-release-execution test]
         [goal r17-claims-audit audit]]]])

(define vor.plan-kind?
  K -> (vor.member? K [generic-proof finite-proof concrete-derivation trace-check test audit]))

(define vor.plan-goals?
  [] -> true
  [[goal Id Kind] | Rest] ->
    (and (vor.names? [Id]) (and (vor.plan-kind? Kind) (vor.plan-goals? Rest)))
  _ -> false)

(define vor.plan-goal-ids
  [] -> []
  [[goal Id _] | Rest] -> [Id | (vor.plan-goal-ids Rest)])

(define vor.plan-disjoint?
  [] _ -> true
  [Id | Rest] Seen -> (and (not (vor.member? Id Seen)) (vor.plan-disjoint? Rest Seen)))

(define vor.plan-valid?
  Stages -> (and (not (= Stages [])) (vor.plan-validate Stages [] [])))

(define vor.plan-validate
  [] _ _ -> true
  [[stage Id Dependencies Goals] | Rest] StageIds GoalIds ->
    (and (vor.names? [Id])
      (and (not (vor.member? Id StageIds))
        (and (vor.proper? Dependencies)
          (and (vor.unique? Dependencies)
            (and (vor.subset? Dependencies StageIds)
              (and (not (= Goals []))
                (and (vor.plan-goals? Goals)
                  (and (vor.unique? (vor.plan-goal-ids Goals))
                    (and (vor.plan-disjoint? (vor.plan-goal-ids Goals) GoalIds)
                         (vor.plan-validate Rest [Id | StageIds]
                           (append GoalIds (vor.plan-goal-ids Goals))))))))))))
  _ _ _ -> false)

(define vor.plan-stage-ids
  [] -> []
  [[stage Id _ _] | Rest] -> [Id | (vor.plan-stage-ids Rest)])

(define vor.plan-open-goals
  [] -> []
  [[stage Stage _ Goals] | Rest] ->
    (append (vor.plan-open-in Stage Goals) (vor.plan-open-goals Rest)))

(define vor.plan-open-in
  _ [] -> []
  Stage [[goal Id Kind] | Rest] ->
    [[obligation Id Stage Kind open] | (vor.plan-open-in Stage Rest)])

(define vor.plan-report
  Stages -> (if (vor.plan-valid? Stages)
                [plan (vor.plan-stage-ids Stages) (vor.plan-open-goals Stages)]
                [rejected malformed-roadmap]))
