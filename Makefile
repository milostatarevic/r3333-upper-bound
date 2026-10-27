PYTHON ?= python3

.PHONY: lean-ci lean-source-audit test-ci
lean-source-audit:
	$(PYTHON) scripts/check_lean_sources.py

test-ci:
	$(PYTHON) -m unittest discover -s scripts -p 'test_*.py' -v
	$(PYTHON) -m unittest discover -s reproduce -p 'test_uniform*.py' -v

lean-ci:
	$(PYTHON) scripts/lean_ci.py
