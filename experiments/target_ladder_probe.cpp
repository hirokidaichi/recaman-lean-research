// Exact-prefix audit of the right-moving ladder countermodel from Round 10.
//
// Reuse the maximal target-comb extractor in the same translation unit, then
// inspect consecutive history-terminated episodes of each fixed mex epoch.

#define main target_comb_extraction_embedded_main
#include "target_comb_extraction_probe.cpp"
#undef main

#include <unordered_map>

namespace {

struct LadderState {
  Episode previous{};
  bool has_previous = false;
  Clock current_streak = 0U;
};

void AnalyzeLadders(Clock horizon) {
  const RunData data = Generate(horizon);
  std::unordered_map<Value, LadderState> states;
  Count edges = 0U;
  Count upward = 0U;
  Count blocker_equals_previous_entry = 0U;
  Count exact_unit_ladder = 0U;
  Count singleton_unit_ladder = 0U;
  Count singleton_episodes = 0U;
  Count parity_failures = 0U;
  Clock maximum_streak = 0U;
  Episode first_exact_previous{}, first_exact_current{};
  bool has_first_exact = false;

  struct FreshInterval {
    Value lower = 0U;
    Value upper = 0U;
    Clock start = 0U;
    Value target = 0U;
    std::size_t episode_index = 0U;
  };
  std::vector<FreshInterval> fresh_intervals;
  fresh_intervals.reserve(data.episodes.size());
  for (std::size_t index = 0U; index < data.episodes.size(); ++index) {
    const Episode& episode = data.episodes[index];
    if (episode.rails == 0U) continue;
    fresh_intervals.push_back(FreshInterval{
        episode.entry - (episode.rails - 1U), episode.entry,
        episode.start, episode.target, index});
  }
  Count blockers_born_on_prior_fresh_rail = 0U;
  Count blockers_born_as_prior_entry = 0U;
  Count blockers_born_as_prior_final_rail = 0U;
  Count blockers_born_on_same_target_rail = 0U;
  Count blockers_born_on_immediate_same_target_previous = 0U;
  Episode first_reuse_episode{};
  FreshInterval first_reuse_origin{};
  std::size_t first_reuse_terminal_index = 0U;
  Clock first_reuse_birth = 0U;
  bool has_first_reuse = false;
  std::unordered_map<Value, std::size_t> previous_history_index;

  for (std::size_t episode_index = 0U;
       episode_index < data.episodes.size(); ++episode_index) {
    const Episode& episode = data.episodes[episode_index];
    LadderState& state = states[episode.target];
    if (episode.kind != EpisodeKind::history_terminal) {
      state = LadderState{};
      previous_history_index.erase(episode.target);
      continue;
    }
    if (episode.rails == 1U) ++singleton_episodes;

    for (const FreshInterval& interval : fresh_intervals) {
      if (episode.blocker < interval.lower ||
          interval.upper < episode.blocker) {
        continue;
      }
      const Clock rail_index =
          static_cast<Clock>(interval.upper - episode.blocker);
      const Clock birth = static_cast<Clock>(interval.start + 2U * rail_index);
      if (birth >= episode.start) continue;
      ++blockers_born_on_prior_fresh_rail;
      if (episode.blocker == interval.upper) ++blockers_born_as_prior_entry;
      if (episode.blocker == interval.lower)
        ++blockers_born_as_prior_final_rail;
      if (episode.target == interval.target)
        ++blockers_born_on_same_target_rail;
      const auto previous = previous_history_index.find(episode.target);
      if (previous != previous_history_index.end() &&
          previous->second == interval.episode_index) {
        ++blockers_born_on_immediate_same_target_previous;
      }
      if (!has_first_reuse) {
        has_first_reuse = true;
        first_reuse_episode = episode;
        first_reuse_origin = interval;
        first_reuse_terminal_index = episode_index;
        first_reuse_birth = birth;
      }
      break;
    }
    if (state.has_previous) {
      const Episode& previous = state.previous;
      ++edges;
      if (previous.blocker < episode.blocker) ++upward;

      const Value entry_difference = episode.entry - previous.entry;
      const Value triangular_difference =
          (static_cast<Value>(episode.start) * (episode.start + 1ULL) -
           static_cast<Value>(previous.start) * (previous.start + 1ULL)) /
          2ULL;
      if ((entry_difference & 1ULL) != (triangular_difference & 1ULL)) {
        ++parity_failures;
      }

      const bool blocker_from_previous_entry =
          episode.blocker == previous.entry;
      const bool exact_unit = blocker_from_previous_entry &&
          episode.entry == previous.entry + 1U;
      if (blocker_from_previous_entry) {
        ++blocker_equals_previous_entry;
      }
      if (exact_unit) {
        ++exact_unit_ladder;
        if (previous.rails == 1U && episode.rails == 1U) {
          ++singleton_unit_ladder;
        }
        ++state.current_streak;
        maximum_streak = std::max(maximum_streak, state.current_streak);
        if (!has_first_exact) {
          has_first_exact = true;
          first_exact_previous = previous;
          first_exact_current = episode;
        }
      } else {
        state.current_streak = 0U;
      }
    }
    state.previous = episode;
    state.has_previous = true;
    previous_history_index[episode.target] = episode_index;
  }

  std::cout << "target-ladder horizon=" << horizon
            << " historyEdges=" << edges << " upward=" << upward << '\n'
            << "  nextBlockerEqPreviousEntry="
            << blocker_equals_previous_entry
            << " exactUnitLadder=" << exact_unit_ladder
            << " singletonUnitLadder=" << singleton_unit_ladder
            << " singletonEpisodes=" << singleton_episodes
            << " maxConsecutiveStreak=" << maximum_streak
            << " parityFailures=" << parity_failures << '\n';
  std::cout << "  blockerBornOnPriorFreshRail="
            << blockers_born_on_prior_fresh_rail
            << " asEntry=" << blockers_born_as_prior_entry
            << " asFinalRail=" << blockers_born_as_prior_final_rail
            << " sameTargetRail=" << blockers_born_on_same_target_rail
            << " immediateSameTargetPrevious="
            << blockers_born_on_immediate_same_target_previous << '\n';
  if (has_first_exact) {
    std::cout << "  first exact: target=" << first_exact_current.target
              << " previous(start/entry/blocker/rails)="
              << first_exact_previous.start << '/'
              << first_exact_previous.entry << '/'
              << first_exact_previous.blocker << '/'
              << first_exact_previous.rails
              << " current(start/entry/blocker/rails)="
              << first_exact_current.start << '/'
              << first_exact_current.entry << '/'
              << first_exact_current.blocker << '/'
              << first_exact_current.rails << '\n';
  }
  if (has_first_reuse) {
    const Episode& origin_episode =
        data.episodes[first_reuse_origin.episode_index];
    std::cout << "  first fresh-rail reuse: blocker="
              << first_reuse_episode.blocker
              << " birth=" << first_reuse_birth
              << " origin(target/start/interval)="
              << first_reuse_origin.target << '/'
              << first_reuse_origin.start << "/["
              << first_reuse_origin.lower << ','
              << first_reuse_origin.upper << "] rails="
              << origin_episode.rails
              << " terminal(target/start/entry)="
              << first_reuse_episode.target << '/'
              << first_reuse_episode.start << '/'
              << first_reuse_episode.entry << " rails="
              << first_reuse_episode.rails << '\n';
    std::cout << "    intervening same-target history episodes:";
    for (std::size_t index = first_reuse_origin.episode_index + 1U;
         index < first_reuse_terminal_index; ++index) {
      const Episode& middle = data.episodes[index];
      if (middle.kind == EpisodeKind::history_terminal &&
          middle.target == first_reuse_episode.target) {
        std::cout << ' ' << middle.start << '/' << middle.entry << '/'
                  << middle.blocker << '/' << middle.rails;
      }
    }
    std::cout << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    AnalyzeLadders(argc >= 2 ? ParseClock(argv[1]) : 5000000U);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
