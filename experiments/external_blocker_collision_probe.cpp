// Exact canonical-orbit falsifier for H-20260902-01.
//
// A positive forced candidate c used at state clock m exposes successor
// demand w=c+m.  If w is already visited, record this as a supplied use.
// A subtraction-born w enters S_c.  For an addition-born w at clock b, the
// positive candidate e=w-2b which forced that birth enters E_c.  Report the
// first candidate reaching four and eight supplied uses without E_c/S_c
// collision.

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();

class DenseHistory {
 public:
  bool Contains(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < seen_.size() &&
           ((seen_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  Clock First(Value value) const {
    const std::size_t index = static_cast<std::size_t>(value);
    return index < first_.size() ? first_[index] : kNoClock;
  }

  bool AdditionBorn(Value value) const {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    return word < addition_born_.size() &&
           ((addition_born_[word] >> (value & 63U)) & 1ULL) != 0U;
  }

  void Record(Value value, Clock clock, bool addition_born) {
    const std::size_t word = static_cast<std::size_t>(value >> 6U);
    if (word >= seen_.size()) {
      seen_.resize(word + 1U, 0U);
      addition_born_.resize(word + 1U, 0U);
    }
    const std::uint64_t mask = 1ULL << (value & 63U);
    if ((seen_[word] & mask) != 0U) return;
    seen_[word] |= mask;
    if (addition_born) addition_born_[word] |= mask;
    const std::size_t index = static_cast<std::size_t>(value);
    if (index >= first_.size()) first_.resize(index + 1U, kNoClock);
    first_[index] = clock;
  }

 private:
  std::vector<std::uint64_t> seen_;
  std::vector<std::uint64_t> addition_born_;
  std::vector<Clock> first_;
};

struct SupplyState {
  std::vector<Clock> uses;
  std::unordered_set<Value> external;
  std::unordered_set<Value> subtractions;
  bool collision = false;
  bool checked4 = false;
  bool checked8 = false;
};

struct Witness {
  bool found = false;
  Value candidate = 0U;
  SupplyState state;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

bool Intersects(const std::unordered_set<Value>& left,
                const std::unordered_set<Value>& right) {
  const auto& small = left.size() <= right.size() ? left : right;
  const auto& large = left.size() <= right.size() ? right : left;
  for (const Value value : small)
    if (large.find(value) != large.end()) return true;
  return false;
}

void PrintWitness(const char* label, const Witness& witness) {
  std::cout << label << '=' << (witness.found ? "REFUTED" : "not-refuted");
  if (!witness.found) {
    std::cout << '\n';
    return;
  }
  std::cout << " candidate=" << witness.candidate << " uses=";
  for (const Clock clock : witness.state.uses) std::cout << clock << ',';
  std::cout << " E=";
  for (const Value value : witness.state.external) std::cout << value << ',';
  std::cout << " S=";
  for (const Value value : witness.state.subtractions) std::cout << value << ',';
  std::cout << '\n';
}

void Run(Clock horizon) {
  DenseHistory history;
  history.Record(0U, 0U, false);
  std::unordered_map<Value, SupplyState> supplies;
  Witness h4, h8;
  Value value = 0U;
  std::uint64_t supplied_uses = 0U;

  for (std::uint64_t raw = 1U; raw <= horizon; ++raw) {
    const Clock use_clock = static_cast<Clock>(raw - 1U);
    const bool positive = value > raw;
    const Value candidate = positive ? value - raw : 0U;
    const bool subtraction = positive && !history.Contains(candidate);
    const bool forced_positive = positive && !subtraction;

    Value exposed = 0U;
    if (subtraction) {
      value = candidate;
    } else {
      if (forced_positive) exposed = value - 1U;
      value += raw;
    }
    history.Record(value, static_cast<Clock>(raw), !subtraction);

    if (!forced_positive || !history.Contains(exposed)) continue;
    ++supplied_uses;
    const Clock birth = history.First(exposed);
    if (birth == kNoClock) throw std::runtime_error("missing first clock");
    SupplyState& state = supplies[candidate];
    state.uses.push_back(use_clock);
    if (history.AdditionBorn(exposed)) {
      const Value twice_birth = 2ULL * birth;
      if (twice_birth < exposed) state.external.insert(exposed - twice_birth);
    } else {
      state.subtractions.insert(exposed);
    }
    state.collision = Intersects(state.external, state.subtractions);

    if (state.uses.size() == 4U && !state.checked4) {
      state.checked4 = true;
      if (!state.collision && !h4.found) h4 = Witness{true, candidate, state};
    }
    if (state.uses.size() == 8U && !state.checked8) {
      state.checked8 = true;
      if (!state.collision && !h8.found) h8 = Witness{true, candidate, state};
    }
  }

  std::uint64_t candidates4 = 0U, candidates8 = 0U, collided = 0U;
  Value most_reused_candidate = 0U;
  std::size_t maximum_supplied_uses = 0U;
  for (const auto& [candidate, state] : supplies) {
    if (state.uses.size() >= 4U) ++candidates4;
    if (state.uses.size() >= 8U) ++candidates8;
    if (state.collision) ++collided;
    if (state.uses.size() > maximum_supplied_uses) {
      maximum_supplied_uses = state.uses.size();
      most_reused_candidate = candidate;
    }
  }
  std::cout << "external-blocker-collision horizon=" << horizon
            << " suppliedUses=" << supplied_uses
            << " candidates=" << supplies.size()
            << " candidates4=" << candidates4
            << " candidates8=" << candidates8
            << " everCollided=" << collided
            << " maxSuppliedUses=" << maximum_supplied_uses
            << " mostReusedCandidate=" << most_reused_candidate << '\n';
  if (maximum_supplied_uses != 0U) {
    const SupplyState& most = supplies.at(most_reused_candidate);
    std::cout << "max-use-detail uses=";
    for (const Clock clock : most.uses) std::cout << clock << ',';
    std::cout << " E=";
    for (const Value member : most.external) std::cout << member << ',';
    std::cout << " S=";
    for (const Value member : most.subtractions) std::cout << member << ',';
    std::cout << '\n';
  }
  PrintWitness("H4", h4);
  PrintWitness("H8", h8);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    Run(argc >= 2 ? ParseClock(argv[1]) : 2000000U);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
