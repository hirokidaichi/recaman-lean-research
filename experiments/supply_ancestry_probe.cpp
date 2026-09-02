// Exact standard-orbit probe for the subtraction-born supplier ancestry.
//
// A positive forced-addition candidate x has a unique first occurrence.  If
// that birth was a legal subtraction at clock b, its predecessor value is
// exactly x + b.  The proposed corridor ancestry would like to charge x to
// that predecessor.  This probe records the two elementary obstructions:
//
//   * the exposure at clock b is legal, not forced, so it is not another
//     node of the forced-candidate supplier theorem;
//   * distinct later forced candidates can have subtraction births from the
//     same predecessor value, so the broadened predecessor map is not
//     injective.
//
// Usage:
//   supply_ancestry_probe END_STEP FIRST_STATE LAST_STATE
//
// The orbit is generated through END_STEP.  Statistics count positive
// forced-candidate uses whose pre-state clock is in the inclusive state
// window [FIRST_STATE, LAST_STATE].

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Count = std::uint64_t;
using Value = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();

class DenseBits {
 public:
  bool Contains(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < words_.size() &&
           ((words_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  void Insert(Value value) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= words_.size()) {
      std::size_t grown = words_.empty() ? 1024U : words_.size();
      while (grown <= word) grown += grown / 2U + 1U;
      words_.resize(grown, 0U);
    }
    words_[word] |= 1ULL << (value & 63U);
  }

 private:
  std::vector<std::uint64_t> words_;
};

class DenseFirstClock {
 public:
  Clock Lookup(Value value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }

  void Record(Value value, Clock clock) {
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) {
      std::size_t grown = first_.empty() ? 1024U : first_.size();
      while (grown <= index) grown += grown / 2U + 1U;
      first_.resize(grown, kNoClock);
    }
    if (first_[index] == kNoClock) first_[index] = clock;
  }

 private:
  std::vector<Clock> first_;
};

struct ForcedChild {
  Value candidate = 0U;
  Clock birth_clock = 0U;
  Clock use_state = 0U;
};

struct SharedParentWitness {
  bool found = false;
  Value parent = 0U;
  ForcedChild first;
  ForcedChild second;
};

Clock ParseClock(const char* text, const char* name) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed > static_cast<unsigned long long>(kNoClock - 1U)) {
    throw std::invalid_argument(std::string(name) + " is too large");
  }
  return static_cast<Clock>(parsed);
}

void RecordChild(
    std::unordered_map<Value, ForcedChild>& first_child,
    SharedParentWitness& witness, Value parent, ForcedChild child) {
  const auto [position, inserted] = first_child.emplace(parent, child);
  if (!inserted && position->second.candidate != child.candidate &&
      !witness.found) {
    witness = {true, parent, position->second, child};
  }
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 4) {
    std::cerr << "usage: supply_ancestry_probe END_STEP FIRST_STATE "
                 "LAST_STATE\n";
    return EXIT_FAILURE;
  }

  try {
    const Clock end_step = ParseClock(argv[1], "END_STEP");
    const Clock first_state = ParseClock(argv[2], "FIRST_STATE");
    const Clock last_state = ParseClock(argv[3], "LAST_STATE");
    if (first_state > last_state || last_state >= end_step) {
      throw std::invalid_argument(
          "require FIRST_STATE <= LAST_STATE < END_STEP");
    }

    DenseBits seen;
    DenseBits subtraction_born;
    DenseFirstClock first_clock;
    seen.Insert(0U);
    first_clock.Record(0U, 0U);

    Value current = 0U;
    std::vector<Value> small_prefix(137U, 0U);

    Count forced_positive = 0U;
    Count addition_born_forced = 0U;
    Count subtraction_born_forced = 0U;
    Count ancestry_clock_violations = 0U;

    bool first_subtraction_forced_found = false;
    ForcedChild first_subtraction_forced;
    Value first_subtraction_parent = 0U;

    std::unordered_map<Value, ForcedChild> global_first_child;
    std::unordered_map<Value, ForcedChild> window_first_child;
    SharedParentWitness global_shared;
    SharedParentWitness window_shared;

    for (Clock step = 1U; step <= end_step; ++step) {
      const Value step_value = static_cast<Value>(step);
      const Value candidate = current > step_value ? current - step_value : 0U;
      const bool can_subtract =
          current > step_value && !seen.Contains(candidate);
      const Clock state_clock = step - 1U;

      if (!can_subtract && current > step_value) {
        const Clock birth = first_clock.Lookup(candidate);
        if (birth == kNoClock) {
          throw std::runtime_error("visited candidate has no first clock");
        }
        const bool born_by_subtraction = subtraction_born.Contains(candidate);
        if (first_state <= state_clock && state_clock <= last_state) {
          ++forced_positive;
          if (born_by_subtraction) {
            ++subtraction_born_forced;
          } else {
            ++addition_born_forced;
          }
        }

        if (born_by_subtraction) {
          const Value parent = candidate + static_cast<Value>(birth);
          const Clock parent_first = first_clock.Lookup(parent);
          if (parent_first == kNoClock || !(parent_first < birth)) {
            ++ancestry_clock_violations;
          }
          const ForcedChild child{candidate, birth, state_clock};
          RecordChild(global_first_child, global_shared, parent, child);
          if (first_state <= state_clock && state_clock <= last_state) {
            RecordChild(window_first_child, window_shared, parent, child);
          }
          if (!first_subtraction_forced_found) {
            first_subtraction_forced_found = true;
            first_subtraction_forced = child;
            first_subtraction_parent = parent;
          }
        }
      }

      const Value next = can_subtract ? candidate : current + step_value;
      if (!seen.Contains(next)) {
        first_clock.Record(next, step);
        if (can_subtract) subtraction_born.Insert(next);
      }
      seen.Insert(next);
      current = next;
      if (step < small_prefix.size()) small_prefix[step] = current;
    }

    std::cout << "window states=[" << first_state << ',' << last_state
              << "] forcedPositive=" << forced_positive
              << " additionBorn=" << addition_born_forced
              << " subtractionBorn=" << subtraction_born_forced << '\n';
    std::cout << "ancestryClockViolations=" << ancestry_clock_violations
              << '\n';

    if (!first_subtraction_forced_found) {
      throw std::runtime_error("no subtraction-born forced candidate found");
    }
    std::cout << "firstSubtractionBornForced candidate="
              << first_subtraction_forced.candidate
              << " birthClock=" << first_subtraction_forced.birth_clock
              << " parent=" << first_subtraction_parent
              << " useState=" << first_subtraction_forced.use_state << '\n';

    if (!global_shared.found) {
      throw std::runtime_error("no shared subtraction parent found");
    }
    std::cout << "firstSharedParent parent=" << global_shared.parent
              << " child1=" << global_shared.first.candidate
              << " birth1=" << global_shared.first.birth_clock
              << " use1=" << global_shared.first.use_state
              << " child2=" << global_shared.second.candidate
              << " birth2=" << global_shared.second.birth_clock
              << " use2=" << global_shared.second.use_state << '\n';

    std::cout << "prefix a109=" << small_prefix[109U]
              << " a110=" << small_prefix[110U]
              << " a113=" << small_prefix[113U]
              << " a125=" << small_prefix[125U]
              << " a126=" << small_prefix[126U]
              << " a133=" << small_prefix[133U] << '\n';

    const Clock parent_birth = first_clock.Lookup(global_shared.parent);
    const Value grandparent =
        global_shared.parent + static_cast<Value>(parent_birth);
    const Clock grandparent_birth = first_clock.Lookup(grandparent);
    std::cout << "sharedParentBirth clock=" << parent_birth
              << " kind="
              << (subtraction_born.Contains(global_shared.parent) ? 'S' : 'A')
              << " predecessor=" << grandparent
              << " predecessorBirth=" << grandparent_birth
              << " predecessorKind="
              << (subtraction_born.Contains(grandparent) ? 'S' : 'A')
              << '\n';

    if (window_shared.found) {
      std::cout << "windowSharedParent parent=" << window_shared.parent
                << " child1=" << window_shared.first.candidate
                << " birth1=" << window_shared.first.birth_clock
                << " use1=" << window_shared.first.use_state
                << " child2=" << window_shared.second.candidate
                << " birth2=" << window_shared.second.birth_clock
                << " use2=" << window_shared.second.use_state << '\n';
    } else {
      std::cout << "windowSharedParent none\n";
    }
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}
