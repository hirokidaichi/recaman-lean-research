#pragma once

// Deterministic empirical certificate rows for
// Recaman.ReplayPrefixSuccessorCoverage.
//
// The rows produced here are discovery/audit data.  They are deliberately
// labelled `empirical`, and are not kernel proofs.  A found successor time is
// nevertheless exact: the orbit is replayed from time zero with exact history,
// so the stored time is its genuine first occurrence.

#include <algorithm>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string_view>
#include <vector>

namespace recaman::prefix_successor {

using Nat = std::uint64_t;

inline constexpr Nat unset = std::numeric_limits<Nat>::max();

class BitSet {
 public:
  [[nodiscard]] bool contains(Nat value) const {
    const Nat word = value >> 6;
    return word < words_.size() &&
           ((words_[word] >> (value & 63)) & 1ULL) != 0;
  }

  void insert(Nat value) {
    const Nat word = value >> 6;
    if (word >= words_.size()) words_.resize(word + 1, 0);
    words_[word] |= 1ULL << (value & 63);
  }

 private:
  std::vector<Nat> words_;
};

struct ExactHistory {
  Nat steps;
  std::vector<Nat> orbit;
  std::vector<Nat> first_occurrence;

  [[nodiscard]] std::optional<Nat> first(Nat value) const {
    if (value >= first_occurrence.size() ||
        first_occurrence[value] == unset) {
      return std::nullopt;
    }
    return first_occurrence[value];
  }
};

inline ExactHistory replay(Nat steps) {
  if (steps == unset) throw std::invalid_argument("steps is too large");

  std::vector<Nat> orbit(steps + 1, 0);
  std::vector<Nat> first_occurrence(1, 0);
  BitSet seen;
  seen.insert(0);

  Nat value = 0;
  for (Nat step = 1; step <= steps; ++step) {
    const bool subtract = value > step && !seen.contains(value - step);
    if (!subtract && value > unset - step) {
      throw std::overflow_error("Recaman orbit value overflow");
    }
    value = subtract ? value - step : value + step;
    orbit[step] = value;
    if (value >= first_occurrence.size()) {
      first_occurrence.resize(value + 1, unset);
    }
    if (!seen.contains(value)) {
      first_occurrence[value] = step;
      seen.insert(value);
    }
  }

  return {steps, std::move(orbit), std::move(first_occurrence)};
}

enum class CoverageStatus {
  covered,
  uncovered_late_first,
  uncovered_value_bound,
  uncovered_unseen,
};

inline std::string_view status_name(CoverageStatus status) {
  switch (status) {
    case CoverageStatus::covered:
      return "covered";
    case CoverageStatus::uncovered_late_first:
      return "uncovered_late_first";
    case CoverageStatus::uncovered_value_bound:
      return "uncovered_value_bound";
    case CoverageStatus::uncovered_unseen:
      return "uncovered_unseen";
  }
  throw std::logic_error("unknown coverage status");
}

struct PrefixSuccessor {
  Nat prefix_time;
  Nat predecessor_value;
  Nat successor_value;
  std::optional<Nat> successor_first;
};

struct CertificateRow {
  Nat orbit_steps;
  Nat clock;
  Nat anchor;
  std::optional<PrefixSuccessor> frontier;
  Nat low_witness_time;
  Nat low_witness_value;
  bool low_witness_at_or_below_anchor;
  Nat uncovered_successor_count;
  CoverageStatus status;
};

inline bool is_eligible_clock(const ExactHistory& history, Nat clock) {
  if (clock >= history.steps) return false;
  const Nat next = clock + 1;
  const Nat anchor = history.orbit[clock];
  return next < anchor && history.orbit[next] == anchor + next;
}

inline CoverageStatus prefix_status(const PrefixSuccessor& prefix,
                                    Nat cutoff) {
  if (!prefix.successor_first) return CoverageStatus::uncovered_unseen;
  if (*prefix.successor_first > cutoff) {
    return CoverageStatus::uncovered_late_first;
  }
  if (prefix.successor_value > cutoff) {
    return CoverageStatus::uncovered_value_bound;
  }
  return CoverageStatus::covered;
}

// Choose the row's frontier deterministically.  An uncovered predecessor is
// preferred to a covered one; within either class, the latest known successor
// first occurrence is preferred.  An unseen successor ranks after every known
// occurrence.  Remaining ties use successor value and then prefix time.
inline bool frontier_precedes(const PrefixSuccessor& lhs,
                              const PrefixSuccessor& rhs, Nat cutoff) {
  const bool lhs_uncovered = prefix_status(lhs, cutoff) != CoverageStatus::covered;
  const bool rhs_uncovered = prefix_status(rhs, cutoff) != CoverageStatus::covered;
  if (lhs_uncovered != rhs_uncovered) return !lhs_uncovered;
  if (lhs.successor_first.has_value() != rhs.successor_first.has_value()) {
    return lhs.successor_first.has_value();
  }
  if (lhs.successor_first &&
      *lhs.successor_first != *rhs.successor_first) {
    return *lhs.successor_first < *rhs.successor_first;
  }
  if (lhs.successor_value != rhs.successor_value) {
    return lhs.successor_value < rhs.successor_value;
  }
  return lhs.prefix_time < rhs.prefix_time;
}

inline std::optional<CertificateRow> analyze(const ExactHistory& history,
                                             Nat clock, Nat cutoff) {
  if (clock >= history.steps) {
    throw std::invalid_argument("clock must be strictly below steps");
  }
  if (cutoff > history.steps) {
    throw std::invalid_argument("cutoff must not exceed steps");
  }
  if (!is_eligible_clock(history, clock)) return std::nullopt;

  const Nat anchor = history.orbit[clock];
  std::optional<PrefixSuccessor> frontier;
  bool all_covered = true;
  std::vector<Nat> uncovered_successors;
  for (Nat time = 0; time < clock; ++time) {
    const Nat predecessor = history.orbit[time];
    if (predecessor <= anchor) continue;
    if (predecessor == unset) {
      throw std::overflow_error("successor value overflow");
    }
    PrefixSuccessor candidate{
        time, predecessor, predecessor + 1, history.first(predecessor + 1)};
    if (prefix_status(candidate, cutoff) != CoverageStatus::covered) {
      all_covered = false;
      if (std::find(uncovered_successors.begin(), uncovered_successors.end(),
                    candidate.successor_value) ==
          uncovered_successors.end()) {
        uncovered_successors.push_back(candidate.successor_value);
      }
    }
    if (!frontier || frontier_precedes(*frontier, candidate, cutoff)) {
      frontier = candidate;
    }
  }

  const CoverageStatus status =
      all_covered ? CoverageStatus::covered : prefix_status(*frontier, cutoff);
  return CertificateRow{history.steps, clock, anchor, frontier, cutoff,
                        history.orbit[cutoff], history.orbit[cutoff] <= anchor,
                        static_cast<Nat>(uncovered_successors.size()), status};
}

inline std::vector<CertificateRow> analyze_range(const ExactHistory& history,
                                                 Nat clock_min,
                                                 Nat clock_max, Nat cutoff) {
  if (clock_min > clock_max) {
    throw std::invalid_argument("clockMin must not exceed clockMax");
  }
  if (clock_max >= history.steps) {
    throw std::invalid_argument("clockMax must be strictly below steps");
  }
  std::vector<CertificateRow> rows;
  for (Nat clock = clock_min; clock <= clock_max; ++clock) {
    if (auto row = analyze(history, clock, cutoff)) {
      rows.push_back(std::move(*row));
    }
  }
  return rows;
}

}  // namespace recaman::prefix_successor
