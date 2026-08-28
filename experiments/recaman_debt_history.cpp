#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct Bits {
  std::vector<std::uint64_t> words;

  bool get(std::uint64_t x) const {
    const std::uint64_t i = x >> 6;
    return i < words.size() && ((words[i] >> (x & 63)) & 1ULL) != 0;
  }

  void set(std::uint64_t x) {
    const std::uint64_t i = x >> 6;
    if (i >= words.size()) words.resize(i + 1, 0);
    words[i] |= 1ULL << (x & 63);
  }
};

struct DiagonalEvent {
  std::uint64_t time = 0;
  std::uint64_t target = 0;
  std::uint64_t tailStart = 0;
  std::uint64_t tailLength = 0;
  std::uint64_t startValue = 0;
  std::uint64_t blocker = 0;
  bool targetSeenByLimit = false;
};

struct DiagonalObservation {
  std::uint64_t time = 0;
  std::uint64_t subtractionTailLength = 0;
  bool successorSeenBefore = false;
};

struct FirstInfo {
  std::uint64_t time = 0;
  char enteredBy = '?';
  bool positiveCandidate = false;
  std::uint64_t candidate = 0;
};

static std::vector<DiagonalEvent> collectDiagonalEvents(
    std::uint64_t limit,
    std::uint64_t& positiveDiagonalStates,
    std::uint64_t& lastPositiveDiagonalTime,
    std::vector<DiagonalObservation>& diagonalObservations) {
  Bits seen;
  seen.set(0);
  std::uint64_t value = 0;
  std::uint64_t subtractionRun = 0;
  std::uint64_t lastAdditionStep = 0;
  std::uint64_t lastAdditionPreValue = 0;
  std::uint64_t lastAdditionValue = 0;
  std::vector<DiagonalEvent> events;
  positiveDiagonalStates = 0;
  lastPositiveDiagonalTime = 0;

  for (std::uint64_t step = 1; step <= limit; ++step) {
    const std::uint64_t oldValue = value;
    const bool subtract = oldValue > step && !seen.get(oldValue - step);
    value = subtract ? oldValue - step : oldValue + step;
    seen.set(value);

    if (subtract) {
      ++subtractionRun;
    } else {
      subtractionRun = 0;
      lastAdditionStep = step;
      lastAdditionPreValue = oldValue;
      lastAdditionValue = value;
    }

    if (value == step) {
      ++positiveDiagonalStates;
      lastPositiveDiagonalTime = step;
      diagonalObservations.push_back(DiagonalObservation{
          step, subtractionRun, seen.get(step + 1)});
    }
    if (value != step || subtractionRun < 2) continue;

    const std::uint64_t tailStart = step - subtractionRun;
    if (lastAdditionStep != tailStart ||
        lastAdditionPreValue <= tailStart) {
      throw std::runtime_error(
          "diagonal maximal-tail invariant failed at time " +
          std::to_string(step));
    }

    const std::uint64_t blocker = lastAdditionPreValue - tailStart;
    if (!seen.get(blocker)) {
      throw std::runtime_error(
          "diagonal blocker was not in history at time " +
          std::to_string(step));
    }

    events.push_back(DiagonalEvent{
        step,
        step + 1,
        tailStart,
        subtractionRun,
        lastAdditionValue,
        blocker,
        false});
  }

  for (auto& event : events) {
    event.targetSeenByLimit = seen.get(event.target);
  }
  return events;
}

static std::unordered_map<std::uint64_t, FirstInfo> discoverFirstInfo(
    std::uint64_t limit,
    const std::unordered_set<std::uint64_t>& roots,
    std::uint64_t maxPasses,
    std::uint64_t& passes,
    std::uint64_t& unresolved) {
  std::unordered_map<std::uint64_t, FirstInfo> result;
  std::unordered_set<std::uint64_t> frontier = roots;
  passes = 0;

  while (!frontier.empty() && passes < maxPasses) {
    ++passes;
    Bits seen;
    seen.set(0);
    std::uint64_t value = 0;
    std::unordered_set<std::uint64_t> found;

    for (std::uint64_t step = 1; step <= limit; ++step) {
      const std::uint64_t oldValue = value;
      const bool subtract = oldValue > step && !seen.get(oldValue - step);
      const std::uint64_t nextValue =
          subtract ? oldValue - step : oldValue + step;
      const bool first = !seen.get(nextValue);

      if (first && frontier.count(nextValue) != 0) {
        const bool positiveCandidate = oldValue > step;
        const std::uint64_t candidate =
            positiveCandidate ? oldValue - step : 0;
        if (!subtract && positiveCandidate && !seen.get(candidate)) {
          throw std::runtime_error(
              "positive forced-addition candidate was not in history at time " +
              std::to_string(step));
        }
        result.emplace(nextValue, FirstInfo{
            step,
            subtract ? '-' : '+',
            positiveCandidate,
            candidate});
        found.insert(nextValue);
      }

      seen.set(nextValue);
      value = nextValue;
    }

    std::unordered_set<std::uint64_t> nextFrontier;
    for (const std::uint64_t current : frontier) {
      const auto it = result.find(current);
      if (it == result.end()) continue;
      const FirstInfo& info = it->second;
      if (info.enteredBy == '+' && info.positiveCandidate &&
          result.count(info.candidate) == 0) {
        nextFrontier.insert(info.candidate);
      }
    }
    frontier = std::move(nextFrontier);
  }

  unresolved = frontier.size();
  return result;
}

static std::string terminalKind(
    const DiagonalEvent& event,
    const std::unordered_map<std::uint64_t, FirstInfo>& firstInfo,
    std::uint64_t& depth) {
  std::uint64_t current = event.blocker;
  depth = 0;

  while (true) {
    const auto it = firstInfo.find(current);
    if (it == firstInfo.end()) return "unresolved_first_info";
    const FirstInfo& info = it->second;
    if (info.enteredBy == '-') return "legal_subtraction";
    if (!info.positiveCandidate) return "nonpositive_candidate";
    ++depth;
    if (info.candidate == event.target) return "target_candidate";
    if (info.candidate < event.target) return "candidate_below_target";
    if (info.candidate >= current) return "nondecreasing_candidate_error";
    current = info.candidate;
  }
}

int main(int argc, char** argv) {
  const std::uint64_t limit =
      argc > 1 ? std::stoull(argv[1]) : 1000000ULL;
  const std::uint64_t maxPasses =
      argc > 2 ? std::stoull(argv[2]) : 64ULL;

  try {
    std::uint64_t positiveDiagonalStates = 0;
    std::uint64_t lastPositiveDiagonalTime = 0;
    std::vector<DiagonalObservation> diagonalObservations;
    std::vector<DiagonalEvent> events = collectDiagonalEvents(
        limit, positiveDiagonalStates, lastPositiveDiagonalTime,
        diagonalObservations);
    std::unordered_set<std::uint64_t> roots;
    for (const auto& event : events) roots.insert(event.blocker);

    std::uint64_t passes = 0;
    std::uint64_t unresolved = 0;
    const auto firstInfo = discoverFirstInfo(
        limit, roots, maxPasses, passes, unresolved);

    std::map<std::string, std::uint64_t> terminalCounts;
    std::uint64_t targetSeen = 0;
    std::uint64_t initialAddition = 0;
    std::uint64_t initialSubtraction = 0;
    std::uint64_t maxDepth = 0;

    std::cout
        << "event,time,target,tail_start,tail_length,start_value,blocker,"
        << "blocker_first_at,blocker_entered_by,first_candidate,"
        << "target_seen_by_limit,chain_depth,terminal\n";

    for (std::size_t i = 0; i < events.size(); ++i) {
      const DiagonalEvent& event = events[i];
      const auto root = firstInfo.find(event.blocker);
      std::uint64_t depth = 0;
      const std::string terminal = terminalKind(event, firstInfo, depth);
      ++terminalCounts[terminal];
      if (event.targetSeenByLimit) ++targetSeen;
      if (root != firstInfo.end()) {
        if (root->second.enteredBy == '+') ++initialAddition;
        if (root->second.enteredBy == '-') ++initialSubtraction;
      }
      if (depth > maxDepth) maxDepth = depth;

      std::cout << i << ',' << event.time << ',' << event.target << ','
                << event.tailStart << ',' << event.tailLength << ','
                << event.startValue << ',' << event.blocker << ',';
      if (root == firstInfo.end()) {
        std::cout << "NA,NA,NA,";
      } else {
        std::cout << root->second.time << ',' << root->second.enteredBy << ',';
        if (root->second.positiveCandidate) {
          std::cout << root->second.candidate << ',';
        } else {
          std::cout << "NA,";
        }
      }
      std::cout << (event.targetSeenByLimit ? 1 : 0) << ',' << depth << ','
                << terminal << '\n';
    }

    std::cerr << "limit=" << limit
              << " positive_diagonal_states=" << positiveDiagonalStates
              << " last_positive_diagonal_time=" << lastPositiveDiagonalTime
              << " debt_eligible_diagonal_events=" << events.size()
              << " distinct_initial_blockers=" << roots.size()
              << " discovery_passes=" << passes
              << " unresolved_after_pass_limit=" << unresolved
              << " target_seen_by_limit=" << targetSeen
              << " initial_entered_by_addition=" << initialAddition
              << " initial_entered_by_subtraction=" << initialSubtraction
              << " max_chain_depth=" << maxDepth << '\n';
    for (const auto& [kind, count] : terminalCounts) {
      std::cerr << "terminal " << kind << '=' << count << '\n';
    }
    for (const auto& observation : diagonalObservations) {
      std::cerr << "diagonal time=" << observation.time
                << " subtraction_tail="
                << observation.subtractionTailLength
                << " successor_seen_before="
                << (observation.successorSeenBefore ? 1 : 0) << '\n';
    }
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return 2;
  }
}
