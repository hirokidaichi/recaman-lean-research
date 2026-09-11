CXX ?= c++
CXXFLAGS ?= -O3 -std=c++20 -Wall -Wextra -Wpedantic
BINDIR ?= bin

TESTS = \
	$(BINDIR)/prefix_successor_certificate_test \
	$(BINDIR)/lean_trace_witness_test \
	$(BINDIR)/balanced_trace_source_test

GENERATORS = \
	$(BINDIR)/prefix_successor_certificate_generator \
	$(BINDIR)/lean_trace_witness_generator \
	$(BINDIR)/balanced_trace_source_generator

CORE_PROBES = \
	$(BINDIR)/recaman_empirical \
	$(BINDIR)/recaman_b1_history \
	$(BINDIR)/recaman_debt_history \
	$(BINDIR)/replay_prefix_successor_coverage \
	$(BINDIR)/blocker_interval_hall \
	$(BINDIR)/blocker_interval_tail \
	$(BINDIR)/causal_blocker_probe \
	$(BINDIR)/target_transition_probe \
	$(BINDIR)/target_right_record_probe \
	$(BINDIR)/use_gap_counterexample \
	$(BINDIR)/periodic_candidate_nogo_check \
	$(BINDIR)/fixed_seed_supply_falsifier \
	$(BINDIR)/run_length_recaman_simulator

.PHONY: all test clean generators probes

all: test

$(BINDIR):
	mkdir -p $(BINDIR)

$(BINDIR)/%: %.cpp | $(BINDIR)
	$(CXX) $(CXXFLAGS) $< -o $@

generators: $(GENERATORS)

probes: $(CORE_PROBES)

test: $(TESTS)
	@echo "Running empirical regression tests..."
	@$(BINDIR)/prefix_successor_certificate_test
	@$(BINDIR)/lean_trace_witness_test
	@$(BINDIR)/balanced_trace_source_test
	@echo "All empirical regression tests passed."

clean:
	rm -rf $(BINDIR)
