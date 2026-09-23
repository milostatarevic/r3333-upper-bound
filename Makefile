PYTHON ?= python3

.PHONY: lean-ci lean-source-audit test-ci
lean-source-audit:
	$(PYTHON) scripts/check_lean_sources.py

test-ci:
	$(PYTHON) -m unittest discover -s scripts -p 'test_*.py' -v
	$(PYTHON) reproduce/test_verify.py
	$(PYTHON) reproduce/test_abd_inputs.py
	$(PYTHON) reproduce/test_abd_native.py

lean-ci:
	$(PYTHON) scripts/lean_ci.py
