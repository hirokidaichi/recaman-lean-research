// Canonical provenance audit for upward target-terminal blocker resets.
//
// This deliberately reuses the exact macro extractor and dense first-origin
// metadata from target_ancestry_capacity_probe.cpp.  The question is whether
// a right-moving terminal ladder must keep manufacturing genuinely new
// ancestry, or can recycle one finite pre-epoch reservoir.

#define main target_ancestry_capacity_embedded_main
#include "target_ancestry_capacity_probe.cpp"
#undef main

#include <map>

namespace {

struct UpwardStats {
  Count edges = 0U;
  Count record_violations = 0U;
  Count first_pre_epoch = 0U;
  Count first_in_epoch = 0U;
  Count first_after_previous_terminal = 0U;
  Count first_origin_addition = 0U;
  Count first_origin_subtraction = 0U;
  Count birth_candidate_pre_epoch = 0U;
  Count birth_candidate_in_epoch = 0U;
  Count birth_candidate_in_prior_hull = 0U;
  Count birth_candidate_above_prior_hull = 0U;
  Count birth_candidate_in_same_target_fresh_interval = 0U;
  Count birth_candidate_in_any_fresh_interval = 0U;
  Count birth_candidate_is_prior_terminal_blocker = 0U;
  Count birth_candidate_is_any_terminal_blocker = 0U;
  Count birth_candidate_is_future_terminal_blocker = 0U;
  Count birth_candidate_is_prior_terminal_entry = 0U;
  Count maximum_fresh_interval_witnesses = 0U;
  Count ancestry_with_subtraction = 0U;
  Count ancestry_all_addition = 0U;
  Count maximum_path_length = 0U;
  Count maximum_subtraction_edges = 0U;
  Count maximum_root_reuse = 0U;
  Count maximum_birth_candidate_reuse = 0U;
};

Clock FirstTime(Value value, const std::vector<std::uint32_t>& metadata) {
  return value == 0U ? 0U : DecodeOrigin(value, metadata).first;
}

void AnalyzeUpwardProvenance(Clock horizon) {
  const MacroData data = GenerateMacroData(horizon);
  const std::vector<std::uint32_t> metadata =
      GenerateFirstMetadata(horizon, data.maximum_value);

  std::unordered_map<Value, TerminalComb> previous;
  std::unordered_map<Value, Value> entry_hull;
  std::unordered_map<Value, Count> root_reuse;
  std::unordered_map<Value, Count> birth_candidate_reuse;
  std::vector<TerminalComb> earlier_terminals;
  std::unordered_map<Value, Clock> first_terminal_use;
  for (const TerminalComb& terminal : data.terminals) {
    auto [position, inserted] =
        first_terminal_use.emplace(terminal.blocker, terminal.start);
    if (!inserted)
      position->second = std::min(position->second, terminal.start);
  }
  UpwardStats stats;

  std::cout << "target-upward-provenance horizon=" << horizon
            << " terminals=" << data.terminals.size() << '\n';

  for (const TerminalComb& terminal : data.terminals) {
    const auto position = previous.find(terminal.target);
    if (position != previous.end()) {
      const TerminalComb& prior = position->second;
      const Value prior_hull = entry_hull.at(terminal.target);
      if (prior.blocker < terminal.blocker) {
        ++stats.edges;
        if (terminal.blocker < prior_hull) ++stats.record_violations;

        const Origin birth = DecodeOrigin(terminal.blocker, metadata);
        const bool birth_subtraction = birth.parent > terminal.blocker;
        if (birth.first <= terminal.epoch_start) {
          ++stats.first_pre_epoch;
        } else {
          ++stats.first_in_epoch;
        }
        if (prior.end < birth.first) ++stats.first_after_previous_terminal;
        if (birth_subtraction) {
          ++stats.first_origin_subtraction;
        } else {
          ++stats.first_origin_addition;
        }

        Value birth_candidate = 0U;
        Clock birth_candidate_first = 0U;
        if (!birth_subtraction) {
          birth_candidate = birth.parent > birth.first
              ? birth.parent - birth.first : 0U;
          birth_candidate_first = FirstTime(birth_candidate, metadata);
          if (birth_candidate_first <= terminal.epoch_start) {
            ++stats.birth_candidate_pre_epoch;
          } else {
            ++stats.birth_candidate_in_epoch;
          }
          if (birth_candidate <= prior_hull) {
            ++stats.birth_candidate_in_prior_hull;
          } else {
            ++stats.birth_candidate_above_prior_hull;
          }
          const Count reuse = ++birth_candidate_reuse[birth_candidate];
          stats.maximum_birth_candidate_reuse =
              std::max(stats.maximum_birth_candidate_reuse, reuse);

          Count interval_witnesses = 0U;
          bool same_target_interval = false;
          bool prior_blocker = false;
          bool prior_entry = false;
          for (const TerminalComb& earlier : earlier_terminals) {
            if (earlier.blocker < birth_candidate &&
                birth_candidate <= earlier.entry) {
              ++interval_witnesses;
              if (earlier.target == terminal.target)
                same_target_interval = true;
            }
            if (birth_candidate == earlier.blocker) prior_blocker = true;
            if (birth_candidate == earlier.entry) prior_entry = true;
          }
          if (same_target_interval)
            ++stats.birth_candidate_in_same_target_fresh_interval;
          if (interval_witnesses != 0U)
            ++stats.birth_candidate_in_any_fresh_interval;
          if (prior_blocker)
            ++stats.birth_candidate_is_prior_terminal_blocker;
          const auto terminal_use = first_terminal_use.find(birth_candidate);
          if (terminal_use != first_terminal_use.end()) {
            ++stats.birth_candidate_is_any_terminal_blocker;
            if (prior.start < terminal_use->second)
              ++stats.birth_candidate_is_future_terminal_blocker;
          }
          if (prior_entry)
            ++stats.birth_candidate_is_prior_terminal_entry;
          stats.maximum_fresh_interval_witnesses = std::max(
              stats.maximum_fresh_interval_witnesses, interval_witnesses);
        }

        Value current = terminal.blocker;
        Count path_length = 0U;
        Count subtraction_edges = 0U;
        while (true) {
          const Origin origin = DecodeOrigin(current, metadata);
          if (origin.first <= terminal.epoch_start) break;
          if (origin.parent > current) ++subtraction_edges;
          current = origin.parent;
          ++path_length;
          if (path_length > horizon)
            throw std::runtime_error("ancestry did not decrease in time");
        }
        if (subtraction_edges == 0U) {
          ++stats.ancestry_all_addition;
        } else {
          ++stats.ancestry_with_subtraction;
        }
        stats.maximum_path_length =
            std::max(stats.maximum_path_length, path_length);
        stats.maximum_subtraction_edges =
            std::max(stats.maximum_subtraction_edges, subtraction_edges);
        const Count root_use = ++root_reuse[current];
        stats.maximum_root_reuse =
            std::max(stats.maximum_root_reuse, root_use);

        std::cout << "  target=" << terminal.target
                  << " starts=" << prior.start << "->" << terminal.start
                  << " blockers=" << prior.blocker << "->"
                  << terminal.blocker << " priorHull=" << prior_hull
                  << " birth=" << birth.first
                  << (birth_subtraction ? "S" : "A")
                  << " parent=" << birth.parent
                  << " forcedCandidate=" << birth_candidate
                  << " candidateFirst=" << birth_candidate_first
                  << " root=" << current << " path=" << path_length
                  << " subEdges=" << subtraction_edges << '\n';
      }
    }
    previous[terminal.target] = terminal;
    auto [hull_position, inserted] =
        entry_hull.emplace(terminal.target, terminal.entry);
    if (!inserted)
      hull_position->second = std::max(hull_position->second, terminal.entry);
    earlier_terminals.push_back(terminal);
  }

  std::cout << "summary upward=" << stats.edges
            << " recordViolations=" << stats.record_violations
            << " first(preEpoch/inEpoch/afterPrevious)="
            << stats.first_pre_epoch << '/' << stats.first_in_epoch << '/'
            << stats.first_after_previous_terminal
            << " origin(add/sub)=" << stats.first_origin_addition << '/'
            << stats.first_origin_subtraction
            << " birthCandidate(preEpoch/inEpoch,inHull/aboveHull,maxReuse)="
            << stats.birth_candidate_pre_epoch << '/'
            << stats.birth_candidate_in_epoch << ','
            << stats.birth_candidate_in_prior_hull << '/'
            << stats.birth_candidate_above_prior_hull << ','
            << stats.maximum_birth_candidate_reuse
            << " freshWitness(sameTarget/any,priorBlocker/anyBlocker/"
               "futureBlocker/entry,maxMultiplicity)="
            << stats.birth_candidate_in_same_target_fresh_interval << '/'
            << stats.birth_candidate_in_any_fresh_interval << '/'
            << stats.birth_candidate_is_prior_terminal_blocker << '/'
            << stats.birth_candidate_is_any_terminal_blocker << '/'
            << stats.birth_candidate_is_future_terminal_blocker << '/'
            << stats.birth_candidate_is_prior_terminal_entry << '/'
            << stats.maximum_fresh_interval_witnesses
            << " ancestry(allAdd/withSub,maxPath/maxSub,maxRootReuse)="
            << stats.ancestry_all_addition << '/'
            << stats.ancestry_with_subtraction << ','
            << stats.maximum_path_length << '/'
            << stats.maximum_subtraction_edges << ','
            << stats.maximum_root_reuse << '\n';

  std::unordered_map<Value, std::vector<std::size_t>> groups;
  for (std::size_t i = 0U; i < data.terminals.size(); ++i)
    groups[data.terminals[i].target].push_back(i);
  AuditTerminalBlockerRemount(data.terminals, groups);
  RemountStats upward_reset_remount;
  for (const auto& [target, indices] : groups) {
    for (std::size_t position = 1U; position < indices.size(); ++position) {
      const TerminalComb& prior = data.terminals[indices[position - 1U]];
      const TerminalComb& current = data.terminals[indices[position]];
      if (prior.blocker < current.blocker) {
        const bool resolved = AddRemountSource(
            target, current.blocker, position, indices, data.terminals,
            upward_reset_remount);
        if (!resolved) {
          const TerminalComb& last = data.terminals[indices.back()];
          std::cout << "  unresolved upward-reset anchor target=" << target
                    << " sourceStart=" << current.start
                    << " anchor=" << current.blocker
                    << " laterEpisodes=" << indices.size() - position - 1U
                    << " lastStart=" << last.start
                    << " lastEntry=" << last.entry
                    << " lastBlocker=" << last.blocker << '\n';
        }
      }
    }
  }
  PrintRemountStats("upward-reset anchor global", upward_reset_remount);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseClock(argv[1]) : 20000000U;
    AnalyzeUpwardProvenance(horizon);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
