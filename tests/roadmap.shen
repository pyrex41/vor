(load "plan/roadmap.shen")

(test.equal roadmap-valid (vor.plan-valid? (vor.roadmap)) true)
(test.equal roadmap-stage-count (length (vor.plan-stage-ids (vor.roadmap))) 18)
(test.equal roadmap-open-count (length (vor.plan-open-goals (vor.roadmap))) 57)
(test.equal roadmap-not-proof (hd (vor.plan-report (vor.roadmap))) plan)
(test.equal roadmap-empty (vor.plan-valid? []) false)
(test.equal roadmap-cycle
  (vor.plan-valid? [[stage a [b] [[goal ga generic-proof]]]
                   [stage b [a] [[goal gb generic-proof]]]]) false)
(test.equal roadmap-self-dependency
  (vor.plan-valid? [[stage a [a] [[goal ga generic-proof]]]]) false)
(test.equal roadmap-duplicate-stage
  (vor.plan-valid? [[stage a [] [[goal ga generic-proof]]]
                   [stage a [] [[goal gb generic-proof]]]]) false)
(test.equal roadmap-duplicate-obligation
  (vor.plan-valid? [[stage a [] [[goal ga generic-proof]]]
                   [stage b [a] [[goal ga generic-proof]]]]) false)
(test.equal roadmap-duplicate-local-obligation
  (vor.plan-valid? [[stage a [] [[goal ga generic-proof] [goal ga generic-proof]]]]) false)
(test.equal roadmap-empty-obligations (vor.plan-valid? [[stage a [] []]]) false)
(test.equal roadmap-wrong-kind
  (vor.plan-valid? [[stage a [] [[goal ga verified]]]]) false)
(test.equal roadmap-improper-dependencies
  (vor.plan-valid? [[stage a [a | garbage] [[goal ga generic-proof]]]]) false)
(test.equal roadmap-no-self-reported-proof
  (vor.plan-valid? [[stage a [] [[goal ga generic-proof passed]]]]) false)
(test.equal roadmap-missing-parent
  (vor.plan-valid? [[stage a [missing] [[goal ga generic-proof]]]]) false)
(test.equal roadmap-forward-parent
  (vor.plan-valid? [[stage b [a] [[goal gb generic-proof]]]
                   [stage a [] [[goal ga generic-proof]]]]) false)
