.PHONY: bootstrap test demo
bootstrap:
	./scripts/bootstrap
test:
	./scripts/shen -l tests/run.shen
demo:
	./scripts/shen -l vor.shen -l examples/mutex.shen -e '(vor.verify (mutex.model) 8)' -e '(vor.verify (mutex.broken) 8)'
