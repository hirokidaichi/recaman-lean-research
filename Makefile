.PHONY: all check test test-probes probes manifest check-manifest clean help

all: check

test: check test-probes check-manifest
	@echo "All Lean, empirical, and viewer checks passed."

check:
	@./scripts/check.sh

test-probes:
	@$(MAKE) -C experiments test

probes:
	@$(MAKE) -C experiments probes

manifest:
	@python3 viewer/gen_manifest.py

check-manifest:
	@python3 viewer/gen_manifest.py --check

clean:
	lake clean
	@$(MAKE) -C experiments clean

help:
	@echo "Recamán Lean Research - make targets:"
	@echo "  make check          - Run Lean builds, architecture check, and axiom audit"
	@echo "  make test           - Run all checks: Lean audit, empirical tests, manifest check"
	@echo "  make test-probes    - Build and run empirical regression tests (experiments/)"
	@echo "  make probes         - Build all core empirical probe binaries (experiments/bin/)"
	@echo "  make manifest       - Regenerate viewer/manifest.json"
	@echo "  make check-manifest - Verify viewer/manifest.json is up to date"
	@echo "  make clean          - Clean Lake build cache and probe binaries"
