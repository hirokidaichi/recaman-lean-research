// Step-word census probe for the actual standard Recamán orbit.
//
// The SAAS theorem (after a legal subtraction, an addition run of length
// exactly 2 is impossible) was first spotted as a gap in a run-length
// histogram.  This probe turns that accident into a systematic census of
// ALL short factors of the step word (A = forced addition, S = legal
// subtraction at that clock): every absent factor is a candidate theorem.
//
// One exact pass to the horizon maintains a rolling 12-bit mask of the
// last steps and counts, for every window length L = 2..12, the number of
// occurrences of each of the 2^L patterns (11 separate count arrays,
// ~64KB total, so the value-visited bitmap dominates memory as usual).
// Windows start at clock 1; the initial forced run AAA is real orbit
// behaviour and is included.  Patterns print with the earlier clock on
// the left, so SAAS means subtract, add, add, subtract.
//
// Report:
//   report1  per L = 2..12: number of absent patterns, with the explicit
//            absent list for L <= 8;
//   report2  full count tables for L <= 5;
//   report3  minimal absent factors up to L = 12 (absent patterns whose
//            proper contiguous subwords are all present);
//   report4  rare occurring patterns of length <= 6 (count < 100) with
//            count and first start clock;
//   sanity   window totals per L, SAAS absent (theorem), SS present
//            (first at clocks 22-23), L = 1 counts near 50/50.
//
// Usage: step_word_census_probe [horizon]

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Clock = std::uint32_t;
using Value = std::uint64_t;
using Count = std::uint64_t;

constexpr Clock kNoClock = std::numeric_limits<Clock>::max();
constexpr std::size_t kMaxWindow = 12U;
constexpr std::size_t kTrackedWindow = 6U;
constexpr std::size_t kListedWindow = 8U;
constexpr std::size_t kTableWindow = 5U;
constexpr Count kRareThreshold = 100U;

constexpr Value kKnownPrefix[16] = {1U,  3U,  6U,  2U,  7U, 13U, 20U, 12U,
                                    21U, 11U, 22U, 10U, 23U, 9U, 24U, 8U};

class DenseSeen {
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

  std::size_t Bytes() const { return words_.size() * sizeof(std::uint64_t); }

 private:
  std::vector<std::uint64_t> words_;
};

Clock ParseClock(const char* text) {
  const unsigned long long parsed = std::stoull(text);
  if (parsed == 0U || parsed > 2000000000ULL)
    throw std::invalid_argument("horizon must be in 1..2,000,000,000");
  return static_cast<Clock>(parsed);
}

double Fraction(Count part, Count whole) {
  return whole == 0U ? 0.0
                     : static_cast<double>(part) / static_cast<double>(whole);
}

std::string PatternString(std::uint32_t pattern, std::size_t length) {
  std::string word(length, 'A');
  for (std::size_t index = 0U; index < length; ++index)
    if (((pattern >> (length - 1U - index)) & 1U) != 0U) word[index] = 'S';
  return word;
}

class StepWordCensus {
 public:
  explicit StepWordCensus(Count horizon) : horizon_(horizon) {
    for (std::size_t length = 2U; length <= kMaxWindow; ++length)
      counts_[length].assign(std::size_t{1U} << length, 0U);
    for (std::size_t length = 1U; length <= kTrackedWindow; ++length)
      first_start_[length].assign(std::size_t{1U} << length, kNoClock);
  }

  void Run() {
    DenseSeen seen;
    seen.Insert(0U);
    Value value = 0U;
    std::uint32_t mask = 0U;

    for (Count raw = 1U; raw <= horizon_; ++raw) {
      const bool positive = value > raw;
      const Value candidate = positive ? value - raw : 0U;
      const bool subtraction = positive && !seen.Contains(candidate);
      if (subtraction) {
        ++subtractions_;
        value = candidate;
      } else {
        ++additions_;
        value += raw;
      }
      maximum_value_ = std::max(maximum_value_, value);
      seen.Insert(value);
      if (raw <= 16U && value != kKnownPrefix[raw - 1U])
        throw std::runtime_error("known prefix mismatch");

      mask = ((mask << 1U) | (subtraction ? 1U : 0U)) &
             ((1U << kMaxWindow) - 1U);
      const std::size_t longest =
          raw < kMaxWindow ? static_cast<std::size_t>(raw) : kMaxWindow;
      for (std::size_t length = 2U; length <= longest; ++length)
        ++counts_[length][mask & ((1U << length) - 1U)];
      const std::size_t tracked = std::min(longest, kTrackedWindow);
      for (std::size_t length = 1U; length <= tracked; ++length) {
        const std::uint32_t pattern = mask & ((1U << length) - 1U);
        if (first_start_[length][pattern] == kNoClock)
          first_start_[length][pattern] =
              static_cast<Clock>(raw - length + 1U);
      }
    }

    final_value_ = value;
    seen_bytes_ = seen.Bytes();
  }

  Count PatternCount(std::size_t length, std::uint32_t pattern) const {
    if (length == 1U) return pattern == 0U ? additions_ : subtractions_;
    return counts_[length][pattern];
  }

  bool IsMinimalAbsent(std::size_t length, std::uint32_t pattern) const {
    if (PatternCount(length, pattern) != 0U) return false;
    for (std::size_t sub = 1U; sub < length; ++sub) {
      for (std::size_t offset = 0U; offset + sub <= length; ++offset) {
        const std::uint32_t subword =
            (pattern >> (length - offset - sub)) & ((1U << sub) - 1U);
        if (PatternCount(sub, subword) == 0U) return false;
      }
    }
    return true;
  }

  void Report(long long elapsed_ms) const {
    std::cout << "step-word-census horizon=" << horizon_
              << " elapsedMs=" << elapsed_ms << '\n';
    std::cout << "  finalValue=" << final_value_
              << " maxValue=" << maximum_value_
              << " seenMB=" << seen_bytes_ / (1024U * 1024U) << '\n';

    ReportSanity();
    ReportAbsent();
    ReportTables();
    ReportMinimalAbsent();
    ReportRare();
  }

 private:
  void ReportSanity() const {
    std::cout << "sanity steps: additions=" << additions_ << " ("
              << Fraction(additions_, horizon_) << ") subtractions="
              << subtractions_ << " (" << Fraction(subtractions_, horizon_)
              << ") total=" << additions_ + subtractions_ << '\n';

    bool totals_ok = additions_ + subtractions_ == horizon_;
    for (std::size_t length = 2U; length <= kMaxWindow; ++length) {
      Count total = 0U;
      for (const Count occurrences : counts_[length]) total += occurrences;
      const Count expected = horizon_ >= length ? horizon_ - length + 1U : 0U;
      if (total != expected) {
        totals_ok = false;
        std::cout << "sanity windowTotal L=" << length << " total=" << total
                  << " expected=" << expected << " MISMATCH" << '\n';
      }
    }
    std::cout << "sanity windowTotals "
              << (totals_ok ? "ok (every L matches horizon-L+1)" : "FAILED")
              << '\n';

    const Count saas = PatternCount(4U, 0b1001U);
    std::cout << "sanity SAAS count=" << saas
              << (saas == 0U ? " (absent, theorem confirmed)"
                             : " (PRESENT, theorem violated!)")
              << '\n';
    const Count ss = PatternCount(2U, 0b11U);
    std::cout << "sanity SS count=" << ss
              << " firstStart=" << first_start_[2U][0b11U]
              << (ss != 0U ? " (present as expected)" : " (MISSING!)") << '\n';
  }

  void ReportAbsent() const {
    for (std::size_t length = 2U; length <= kMaxWindow; ++length) {
      std::size_t absent = 0U;
      for (const Count occurrences : counts_[length])
        if (occurrences == 0U) ++absent;
      std::cout << "report1 L=" << length << " patterns="
                << (std::size_t{1U} << length) << " absent=" << absent;
      if (length <= kListedWindow && absent != 0U) {
        std::cout << " list:";
        for (std::uint32_t pattern = 0U;
             pattern < (1U << length); ++pattern)
          if (counts_[length][pattern] == 0U)
            std::cout << ' ' << PatternString(pattern, length);
      }
      std::cout << '\n';
    }
  }

  void ReportTables() const {
    for (std::size_t length = 2U; length <= kTableWindow; ++length) {
      std::cout << "report2 countTable L=" << length << ':';
      for (std::uint32_t pattern = 0U; pattern < (1U << length); ++pattern)
        std::cout << ' ' << PatternString(pattern, length) << '='
                  << counts_[length][pattern];
      std::cout << '\n';
    }
  }

  void ReportMinimalAbsent() const {
    std::cout << "report3 minimalAbsent (no proper contiguous subword is"
                 " absent):";
    std::size_t found = 0U;
    for (std::size_t length = 2U; length <= kMaxWindow; ++length)
      for (std::uint32_t pattern = 0U; pattern < (1U << length); ++pattern)
        if (IsMinimalAbsent(length, pattern)) {
          std::cout << ' ' << PatternString(pattern, length);
          ++found;
        }
    if (found == 0U) std::cout << " (none)";
    std::cout << '\n';
    std::cout << "report3 minimalAbsentCount=" << found << '\n';
  }

  void ReportRare() const {
    std::cout << "report4 rare occurring patterns (length<=" << kTrackedWindow
              << ", 0<count<" << kRareThreshold << "):" << '\n';
    std::size_t found = 0U;
    for (std::size_t length = 2U; length <= kTrackedWindow; ++length)
      for (std::uint32_t pattern = 0U; pattern < (1U << length); ++pattern) {
        const Count occurrences = counts_[length][pattern];
        if (occurrences == 0U || occurrences >= kRareThreshold) continue;
        std::cout << "report4   " << PatternString(pattern, length)
                  << " count=" << occurrences
                  << " firstStart=" << first_start_[length][pattern] << '\n';
        ++found;
      }
    if (found == 0U) std::cout << "report4   (none)" << '\n';
  }

  Count horizon_;
  Count additions_ = 0U;
  Count subtractions_ = 0U;
  Value final_value_ = 0U;
  Value maximum_value_ = 0U;
  std::size_t seen_bytes_ = 0U;
  std::array<std::vector<Count>, kMaxWindow + 1U> counts_;
  std::array<std::vector<Clock>, kTrackedWindow + 1U> first_start_;
};

void AnalyzeStepWord(Clock horizon) {
  const auto started = std::chrono::steady_clock::now();
  StepWordCensus census(horizon);
  census.Run();
  const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - started);
  census.Report(elapsed.count());
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseClock(argv[1]) : 100000000U;
    AnalyzeStepWord(horizon);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
