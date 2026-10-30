.PHONY: bootstrap test demo plan boundary-demo test-kernel logic-demo test-service program-demo test-effects-protocol export-effects-model
bootstrap:
	./scripts/bootstrap
test:
	./scripts/shen -l tests/run.shen

test-effects-protocol:
	./scripts/shen -l tests/effects-protocol.shen

export-effects-model:
	./scripts/export-effects-model --mode healthy --output .work/effects-model.json
demo:
	./scripts/shen -l vor.shen -l examples/mutex.shen -e '(vor.verify (mutex.model) 8)' -e '(vor.verify (mutex.broken) 8)'
plan:
	./scripts/shen -l vor.shen -l plan/roadmap.shen -e '(vor.plan-report (vor.roadmap))'

boundary-demo:
	./scripts/shen -l vor.shen -l examples/mutex.shen -l examples/claim.shen -e '(claim-demo.run)'

test-kernel:
	./scripts/test-kernel

logic-demo:
	./scripts/shen -l vor.shen -l examples/first-order.shen -e '(fol-demo.check)' -e '(fol-demo.typed)'

test-service:
	python3 -m unittest discover -s tests -p test_service.py -v

program-demo:
	./scripts/shen -l vor.shen -l examples/program.shen -e '(program-demo.run)'

.PHONY: admission-demo
admission-demo:
	./scripts/shen -l vor.shen -l examples/admission.shen -e '(admission-demo.check)' -e '(vor.run-admitted (admission-demo.program) (admission-demo.signature) (admission-demo.contracts) (admission-demo.evidence) total.twice [[succ [succ zero]]] 2000 1000)'

.PHONY: test-construction-mutations
test-construction-mutations:
	./scripts/test-construction-mutations

.PHONY: bootstrap-audit test-metatheory compiler-demo
bootstrap-audit:
	./scripts/bootstrap-audit

test-metatheory:
	./scripts/test-metatheory

compiler-demo:
	./scripts/shen -l vor.shen -l examples/admission.shen -e '(vor.compiled-outcome (admission-demo.program) (hd (tl (vor.compile-program (admission-demo.program)))) total.twice [[succ [succ zero]]] 2000)'

.PHONY: cases-demo
cases-demo:
	./scripts/shen -l vor.shen -l examples/scoping.shen -e '(scoping.run)'
