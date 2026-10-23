.PHONY: bootstrap test demo plan
bootstrap:
	./scripts/bootstrap
test:
	./scripts/shen -l tests/run.shen
demo:
	./scripts/shen -l vor.shen -l examples/mutex.shen -e '(vor.verify (mutex.model) 8)' -e '(vor.verify (mutex.broken) 8)'
plan:
	./scripts/shen -l vor.shen -l plan/roadmap.shen -e '(vor.plan-report (vor.roadmap))'
