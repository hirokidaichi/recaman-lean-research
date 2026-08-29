// Replay fixed point scan.
//
// The Lean development reduces a hypothetical missing target m to an "exact
// replay fixed point" whose crossing clock C must satisfy:
//   (1) C >= 6
//   (2) C + 1 < a(C)                        (crossing value above its clock)
//   (3) a(C+1) = a(C) + (C+1)               (actual step is a forced addition)
//   (4) a(C) < T <= a(C+1)                  (band straddles the target)
//   (5) T never occurs in the orbit
//   (6) blocker v = a(C) - (C+1) > 0 first occurs at firstTime < C, and some
//       fresh landing e <= C has a(e) < T with C the FIRST weak upcrossing
//       from e (no t in [e, C) with a(t) < T <= a(t+1)).
// This program enumerates clocks C in [6, Cmax] against the real orbit up to
// N steps and reports which (C, T) pairs survive, plus how deep into the
// orbit a Lean kernel `decide` would have to look to kill each candidate.
//
// Usage: replay_scan [N=10000000] [Cmax=10000]

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

struct BitSet {
  std::vector<std::uint64_t> words;
  bool get(std::uint64_t x) const {
    const std::uint64_t i = x >> 6;
    return i < words.size() && ((words[i] >> (x & 63)) & 1ULL);
  }
  void set(std::uint64_t x) {
    const std::uint64_t i = x >> 6;
    if (i >= words.size()) words.resize(i + 1, 0);
    words[i] |= 1ULL << (x & 63);
  }
};

static constexpr std::uint64_t kUnset =
    std::numeric_limits<std::uint64_t>::max();

static int bucketOf(std::uint64_t f) {
  static const std::uint64_t edges[] = {100, 200, 500, 1000, 5000,
                                        10000, 100000, 1000000, 10000000};
  if (f == kUnset) return 10;
  for (int i = 0; i < 9; ++i)
    if (f <= edges[i]) return i;
  return 9;
}

static const char* const kBucketNames[] = {
    "<=100", "<=200", "<=500", "<=1e3", "<=5e3", "<=1e4",
    "<=1e5", "<=1e6", "<=1e7", ">1e7", "unseen"};

int main(int argc, char** argv) {
  const auto t0 = std::chrono::steady_clock::now();
  const std::uint64_t N = argc > 1 ? std::stoull(argv[1]) : 10000000ULL;
  std::uint64_t Cmax = argc > 2 ? std::stoull(argv[2]) : 10000ULL;
  if (Cmax + 1 > N) Cmax = N > 0 ? N - 1 : 0;

  // Pass 1: orbit head a(0..Cmax+1), to size the first-occurrence table.
  std::vector<std::uint64_t> head(Cmax + 2, 0);
  {
    BitSet headSeen;
    headSeen.set(0);
    std::uint64_t a = 0;
    for (std::uint64_t step = 1; step <= Cmax + 1; ++step) {
      const bool subtract = a > step && !headSeen.get(a - step);
      a = subtract ? a - step : a + step;
      headSeen.set(a);
      head[step] = a;
    }
  }
  std::uint64_t bandMax = 0;
  for (const std::uint64_t x : head) bandMax = std::max(bandMax, x);

  // Pass 2: full orbit up to N, recording first occurrences of small values.
  std::vector<std::uint64_t> firstOcc(bandMax + 1, kUnset);
  firstOcc[0] = 0;
  BitSet seen;
  seen.set(0);
  std::uint64_t a = 0, maxA = 0, distinctA = 1;
  for (std::uint64_t step = 1; step <= N; ++step) {
    const bool subtract = a > step && !seen.get(a - step);
    a = subtract ? a - step : a + step;
    if (!seen.get(a)) {
      distinctA++;
      if (a <= bandMax) firstOcc[a] = step;
      seen.set(a);
    }
    maxA = std::max(maxA, a);
    if (step <= Cmax + 1 && head[step] != a) {
      std::cerr << "head mismatch at " << step << "\n";
      return 2;
    }
  }

  // Analysis over clocks C in [6, Cmax].
  std::uint64_t cond2Count = 0, qualCount = 0, qualFreshC = 0;
  std::uint64_t vFirstAnomalies = 0;
  double ratioSum = 0, ratioMin = 1e300, ratioMax = 0;
  std::vector<std::uint64_t> qualPerBlock(Cmax / 1000 + 1, 0);

  std::uint64_t totalTargets = 0;
  std::uint64_t targetBuckets[11] = {0};
  std::uint64_t maxSeenFirst = 0, maxSeenFirstC = 0, maxSeenFirstT = 0;

  std::uint64_t bandBuckets[11] = {0};  // per-C max first occurrence in band
  std::uint64_t covered100Max = 0, covered100Count = 0;
  std::uint64_t covered200Max = 0, covered200Count = 0;
  std::uint64_t covered1000Max = 0, covered1000Count = 0;
  std::uint64_t bandsWithUnseen = 0;

  std::uint64_t noLandingPairs = 0, unseenPairs = 0, survivorPairs = 0;
  std::vector<std::string> noLandingRows, survivorRows, qualRows, notableRows;
  std::vector<std::uint64_t> unseenTs;  // one entry per unseen (C, T) pair

  std::vector<std::int64_t> lastUp;
  std::vector<std::uint64_t> sufMinFresh;

  for (std::uint64_t C = 6; C <= Cmax; ++C) {
    const std::uint64_t aC = head[C], aC1 = head[C + 1];
    if (C + 1 >= aC) continue;
    cond2Count++;
    if (aC1 != aC + (C + 1)) continue;  // subtraction fired: not forced add
    qualCount++;
    qualPerBlock[C / 1000]++;
    const double ratio = static_cast<double>(aC) / static_cast<double>(C + 1);
    ratioSum += ratio;
    ratioMin = std::min(ratioMin, ratio);
    ratioMax = std::max(ratioMax, ratio);
    const std::uint64_t v = aC - (C + 1);
    const std::uint64_t vFirst = firstOcc[v];
    if (!(vFirst < C)) vFirstAnomalies++;
    const bool freshC = firstOcc[aC] == C;
    if (freshC) qualFreshC++;

    // Band target first occurrences.
    std::uint64_t bandMaxFirst = 0, bandUnseen = 0;
    for (std::uint64_t T = aC + 1; T <= aC1; ++T) {
      const std::uint64_t f = firstOcc[T];
      totalTargets++;
      targetBuckets[bucketOf(f)]++;
      if (f == kUnset) {
        bandUnseen++;
      } else {
        bandMaxFirst = std::max(bandMaxFirst, f);
        if (f > maxSeenFirst) {
          maxSeenFirst = f;
          maxSeenFirstC = C;
          maxSeenFirstT = T;
        }
      }
    }
    bandBuckets[bucketOf(bandUnseen ? kUnset : bandMaxFirst)]++;
    if (bandUnseen == 0) {
      if (bandMaxFirst <= 100) { covered100Max = C; covered100Count++; }
      if (bandMaxFirst <= 200) { covered200Max = C; covered200Count++; }
      if (bandMaxFirst <= 1000) { covered1000Max = C; covered1000Count++; }
    } else {
      bandsWithUnseen++;
    }

    // Condition 6 landing structure: last weak upcrossing before C per T,
    // and the suffix minimum of fresh orbit values over e in [0, C].
    const std::uint64_t W = C + 1;
    lastUp.assign(W, -1);
    for (std::uint64_t t = 0; t < C; ++t) {
      if (head[t] >= head[t + 1]) continue;
      const std::uint64_t lo = std::max(head[t] + 1, aC + 1);
      const std::uint64_t hi = std::min(head[t + 1], aC1);
      for (std::uint64_t T = lo; T <= hi; ++T)
        lastUp[T - (aC + 1)] = static_cast<std::int64_t>(t);
    }
    sufMinFresh.assign(C + 2, kUnset);
    for (std::uint64_t e = C + 1; e-- > 0;) {
      const std::uint64_t val = firstOcc[head[e]] == e ? head[e] : kUnset;
      sufMinFresh[e] = std::min(val, sufMinFresh[e + 1]);
    }
    std::uint64_t bandNoLanding = 0;
    for (std::uint64_t j = 0; j < W; ++j) {
      const std::uint64_t T = aC + 1 + j;
      const std::uint64_t eLow = static_cast<std::uint64_t>(lastUp[j] + 1);
      const bool landingExists = sufMinFresh[eLow] < T;
      if (!landingExists) {
        bandNoLanding++;
        noLandingPairs++;
        if (noLandingRows.size() < 40) {
          noLandingRows.push_back(std::to_string(C) + "," +
            std::to_string(T) + "," + std::to_string(lastUp[j]) + "," +
            (firstOcc[T] == kUnset ? std::string("unseen")
                                   : std::to_string(firstOcc[T])));
        }
      }
      if (firstOcc[T] == kUnset) {
        unseenPairs++;
        unseenTs.push_back(T);
        std::uint64_t landings = 0;
        for (std::uint64_t e = eLow; e <= C; ++e)
          if (firstOcc[head[e]] == e && head[e] < T) landings++;
        if (landings > 0) survivorPairs++;
        if (survivorRows.size() < 200) {
          survivorRows.push_back(std::to_string(C) + "," +
            std::to_string(aC) + "," + std::to_string(aC1) + "," +
            std::to_string(T) + "," + std::to_string(v) + "," +
            std::to_string(vFirst) + "," + std::to_string(landings) + "," +
            (landings > 0 ? "SURVIVES" : "no_landing"));
        }
      }
    }

    const std::string row = std::to_string(C) + "," + std::to_string(aC) +
        "," + std::to_string(aC1) + "," + std::to_string(v) + "," +
        std::to_string(vFirst) + "," + (freshC ? "fresh" : "dup") + "," +
        (bandUnseen ? std::string("unseen") : std::to_string(bandMaxFirst)) +
        "," + std::to_string(bandUnseen) + "," +
        std::to_string(bandNoLanding);
    if (qualRows.size() < 40) qualRows.push_back(row);
    if ((bandUnseen > 0 || !freshC || bandNoLanding > 0 ||
         bandMaxFirst > 5000) && notableRows.size() < 60)
      notableRows.push_back(row);
  }

  const double secs = std::chrono::duration<double>(
      std::chrono::steady_clock::now() - t0).count();

  std::cout << "N=" << N << " Cmax=" << Cmax << " maxA=" << maxA
            << " distinctA=" << distinctA << " bandMax=" << bandMax
            << " bitsetMB=" << std::fixed << std::setprecision(2)
            << seen.words.size() * 8.0 / 1024 / 1024
            << " secs=" << secs << "\n";
  std::cout << "clocks cond2=" << cond2Count << " cond2+3=" << qualCount
            << " freshC=" << qualFreshC
            << " vFirst_anomalies=" << vFirstAnomalies << "\n";
  std::cout << "ratio_aC_over_C1 min=" << std::setprecision(4) << ratioMin
            << " mean=" << (qualCount ? ratioSum / qualCount : 0.0)
            << " max=" << ratioMax << "\n";
  std::cout << "qualifying_per_1000";
  for (std::size_t i = 0; i < qualPerBlock.size(); ++i)
    std::cout << " [" << i << "k)=" << qualPerBlock[i];
  std::cout << "\n";
  std::cout << "target_first_occurrence total=" << totalTargets;
  for (int i = 0; i < 11; ++i)
    std::cout << " " << kBucketNames[i] << "=" << targetBuckets[i];
  std::cout << "\n";
  std::cout << "max_seen_first=" << maxSeenFirst
            << " at C=" << maxSeenFirstC << " T=" << maxSeenFirstT << "\n";
  std::cout << "band_max_first_per_C";
  for (int i = 0; i < 11; ++i)
    std::cout << " " << kBucketNames[i] << "=" << bandBuckets[i];
  std::cout << "\n";
  std::cout << "band_covered_by_100 count=" << covered100Count
            << " largest_C=" << covered100Max << "\n";
  std::cout << "band_covered_by_200 count=" << covered200Count
            << " largest_C=" << covered200Max << "\n";
  std::cout << "band_covered_by_1000 count=" << covered1000Count
            << " largest_C=" << covered1000Max << "\n";
  std::cout << "bands_with_unseen_target=" << bandsWithUnseen
            << " unseen_pairs=" << unseenPairs
            << " no_landing_pairs=" << noLandingPairs
            << " SURVIVOR_PAIRS=" << survivorPairs << "\n";
  std::sort(unseenTs.begin(), unseenTs.end());
  std::uint64_t distinctUnseenT = 0;
  std::vector<std::string> unseenTRows;
  for (std::size_t i = 0; i < unseenTs.size();) {
    std::size_t j = i;
    while (j < unseenTs.size() && unseenTs[j] == unseenTs[i]) j++;
    distinctUnseenT++;
    if (unseenTRows.size() < 60)
      unseenTRows.push_back(std::to_string(unseenTs[i]) + " x" +
                            std::to_string(j - i));
    i = j;
  }
  std::cout << "distinct_unseen_targets=" << distinctUnseenT << "\n";
  std::cout << "unseen_target_bandcounts";
  for (const auto& row : unseenTRows) std::cout << " " << row;
  std::cout << "\n";
  std::cout << "first_actual_missing";
  for (std::uint64_t x = 0, found = 0; found < 20 && x <= maxA; ++x)
    if (!seen.get(x)) { std::cout << " " << x; found++; }
  std::cout << "\n";
  std::cout << "survivor_rows C,aC,aC1,T,v,vFirst,landings,verdict\n";
  for (const auto& row : survivorRows) std::cout << row << "\n";
  std::cout << "no_landing_rows C,T,lastUpBeforeC,firstOccT\n";
  for (const auto& row : noLandingRows) std::cout << row << "\n";
  std::cout << "qualifying_sample C,aC,aC1,v,vFirst,freshC,bandMaxFirst,"
            << "bandUnseen,bandNoLanding\n";
  for (const auto& row : qualRows) std::cout << row << "\n";
  std::cout << "notable_rows same_columns\n";
  for (const auto& row : notableRows) std::cout << row << "\n";
}
