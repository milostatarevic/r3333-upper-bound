PYTHON ?= python3

.PHONY: audit-sources test-ci lean-ci lean-full

audit-sources:
	$(PYTHON) -B scripts/check_lean_sources.py

test-ci:
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -B -m unittest discover -s scripts -p 'test_lean_audits.py' -v

lean-ci:
	$(PYTHON) -B scripts/lean_ci.py

lean-full:
	$(PYTHON) -B scripts/lean_ci.py --full
