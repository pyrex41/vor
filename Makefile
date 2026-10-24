.PHONY: bootstrap test demo plan boundary-demo test-kernel logic-demo test-service
bootstrap:
	./scripts/bootstrap
test:
	./scripts/shen -l tests/run.shen
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
