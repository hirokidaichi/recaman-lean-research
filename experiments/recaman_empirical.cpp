#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
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

struct StateData {
  std::uint64_t a = 0, q = 0, r = 0;
  std::int64_t G = 0;
};

static StateData coords(std::uint64_t n, std::uint64_t a) {
  StateData z;
  z.a = a;
  z.q = a / n;
  z.r = a % n;
  z.G = static_cast<std::int64_t>(z.r) -
        static_cast<std::int64_t>(z.q * (z.q + 1) / 2);
  return z;
}

struct Episode {
  std::uint64_t start = 0, end = 0, length = 0;
  std::int64_t minG = 0;
  std::uint64_t minAt = 0, startQ = 0, endQ = 0;
  bool recovered = false;
  std::uint64_t firstB1 = std::numeric_limits<std::uint64_t>::max();
  std::uint64_t firstB1Cross = std::numeric_limits<std::uint64_t>::max();
  std::string path;
};

struct TargetCandidate {
  std::uint64_t start = 0, due = 0, m = 0, q = 0;
  bool fresh = false, allSubtract = true;
  std::uint64_t failAt = 0, blockerY = 0;
};

int main(int argc, char** argv) {
  std::uint64_t N = argc > 1 ? std::stoull(argv[1]) : 1000000ULL;
  const std::uint64_t watchM = argc > 2 ? std::stoull(argv[2]) : 852ULL;
  BitSet seen;
  seen.set(0);
  std::uint64_t a = 0, maxA = 0, maxQ = 0, maxQAt = 0, distinctA = 1;
  std::int64_t minG = 0, maxG = 0;
  std::uint64_t minGAt = 0, maxGAt = 0;
  std::map<std::uint64_t, std::uint64_t> bCount;
  std::map<std::uint64_t, std::uint64_t> qCount;
  std::uint64_t negativeStates = 0, nonnegativeStates = 0;
  std::uint64_t negToNonneg = 0, nonnegToNeg = 0;
  std::uint64_t b1NegTransitions = 0, b1NegCross = 0;
  std::uint64_t addCross = 0, subCross = 0;
  std::uint64_t q2Cross = 0, q3Cross = 0, qOtherCross = 0;
  std::uint64_t q2Nonneg = 0, q3Nonneg = 0;
  std::uint64_t q2FreshM = 0, q2FreshBoth = 0;
  std::uint64_t q3FreshM = 0;
  std::map<std::uint64_t, std::uint64_t> targetTotal, targetFresh,
      targetSuccess, targetFreshSuccess;
  BitSet distinctGateM;
  BitSet allLevels, q1Levels, q2Levels, q3Levels;
  std::uint64_t allLevelCount = 0, q1LevelCount = 0, q2LevelCount = 0,
      q3LevelCount = 0;
  std::uint64_t distinctGateMCount = 0, maxGateM = 0;
  std::vector<std::string> gateRows;
  std::vector<TargetCandidate> activeTargets;
  std::vector<std::string> target852Rows;
  std::uint64_t maxB = 0, maxBAt = 0;
  std::uint64_t maxNegEpisodeLen = 0, maxNegEpisodeStart = 0;
  std::vector<Episode> episodes;
  std::vector<std::string> crossingRows;
  std::vector<std::string> firstBRows;

  bool inNeg = false;
  Episode current;
  StateData prev;

  for (std::uint64_t step = 1; step <= N; ++step) {
    const std::uint64_t oldA = a;
    const bool subtract = a > step && !seen.get(a - step);
    const std::uint64_t nextA = subtract ? a - step : a + step;
    if (!seen.get(nextA)) distinctA++;
    seen.set(nextA);
    a = nextA;
    maxA = std::max(maxA, a);
    StateData z = coords(step, a);

    for (auto& c : activeTargets) {
      if (!subtract && c.allSubtract) {
        c.allSubtract = false;
        c.failAt = step;
        c.blockerY = oldA >= step ? oldA - step : 0;
      }
    }
    for (std::size_t i = 0; i < activeTargets.size();) {
      const auto& c = activeTargets[i];
      if (c.due == step) {
        const bool success = c.allSubtract && a == c.m;
        if (success) targetSuccess[c.q]++;
        if (success && c.fresh) targetFreshSuccess[c.q]++;
        if (c.m == watchM && target852Rows.size() < 100) {
          target852Rows.push_back(std::to_string(c.start) + "," +
            std::to_string(c.q) + "," + (c.fresh ? "fresh" : "seen") +
            "," + (success ? "success" : "blocked") + "," +
            std::to_string(c.failAt) + "," + std::to_string(c.blockerY));
        }
        activeTargets.erase(activeTargets.begin() + i);
      } else {
        ++i;
      }
    }
    qCount[z.q]++;
    if (z.q > maxQ) { maxQ = z.q; maxQAt = step; }
    if (z.G < minG) { minG = z.G; minGAt = step; }
    if (z.G > maxG) { maxG = z.G; maxGAt = step; }
    if (z.G < 0) negativeStates++; else nonnegativeStates++;

    if (z.G >= 0 && z.q == 2) {
      q2Nonneg++;
      const std::uint64_t m = static_cast<std::uint64_t>(z.G);
      const bool mfresh = !seen.get(m) || m == a;
      const std::uint64_t intermediate = step + m + 2;
      const bool ifresh = !seen.get(intermediate) || intermediate == a;
      if (mfresh) q2FreshM++;
      if (mfresh && ifresh) q2FreshBoth++;
      if (mfresh && ifresh) {
        if (!distinctGateM.get(m)) {
          distinctGateM.set(m);
          distinctGateMCount++;
          maxGateM = std::max(maxGateM, m);
        }
        if (gateRows.size() < 30 || step > N - 1000000) {
          if (gateRows.size() < 60)
            gateRows.push_back(std::to_string(step) + "," +
              std::to_string(m) + "," + std::to_string(a) + "," +
              std::to_string(intermediate));
        }
      }
    }
    if (z.G >= 0 && z.q == 3) {
      q3Nonneg++;
      const std::uint64_t m = static_cast<std::uint64_t>(z.G);
      if (!seen.get(m) || m == a) q3FreshM++;
    }
    if (z.G >= 0 && z.q > 0) {
      const std::uint64_t m = static_cast<std::uint64_t>(z.G);
      const bool fresh = !seen.get(m);
      if (!allLevels.get(m)) { allLevels.set(m); allLevelCount++; }
      if (z.q == 1 && !q1Levels.get(m)) { q1Levels.set(m); q1LevelCount++; }
      if (z.q == 2 && !q2Levels.get(m)) { q2Levels.set(m); q2LevelCount++; }
      if (z.q == 3 && !q3Levels.get(m)) { q3Levels.set(m); q3LevelCount++; }
      targetTotal[z.q]++;
      if (fresh) targetFresh[z.q]++;
      if (step + z.q <= N)
        activeTargets.push_back(TargetCandidate{step, step + z.q, m, z.q, fresh, true});
    }

    if (step == 1) {
      if (z.G < 0) {
        inNeg = true;
        current = Episode{step, step, 1, z.G, step, z.q, z.q, false};
      }
      prev = z;
      continue;
    }

    const std::uint64_t n = step - 1;
    const std::uint64_t d = prev.q > prev.r ? prev.q - prev.r : 0;
    const std::uint64_t b = d == 0 ? 0 : (d + n) / (n + 1);
    const std::uint64_t s = b * (n + 1) + prev.r - prev.q;
    bCount[b]++;
    if (b > maxB) { maxB = b; maxBAt = n; }
    if (s != z.r) {
      std::cerr << "remainder mismatch at " << n << "\n";
      return 2;
    }
    const std::uint64_t expectedQ = subtract ? prev.q - 1 - b : prev.q + 1 - b;
    if (expectedQ != z.q) {
      std::cerr << "quotient mismatch at " << n << " branch=" << subtract
                << " q=" << prev.q << " b=" << b << " got=" << z.q
                << " expected=" << expectedQ << "\n";
      return 3;
    }

    if (prev.G < 0 && b == 1) {
      b1NegTransitions++;
      if (current.firstB1 == std::numeric_limits<std::uint64_t>::max()) {
        current.firstB1 = n;
        if (firstBRows.size() < 25) {
          firstBRows.push_back(std::to_string(current.start) + "," +
            std::to_string(n) + "," + (subtract ? "-" : "+") + "," +
            std::to_string(prev.q) + "," + std::to_string(prev.r) + "," +
            std::to_string(prev.G) + "," + std::to_string(z.q) + "," +
            std::to_string(z.r) + "," + std::to_string(z.G));
        }
      }
    }
    if (prev.G < 0 && inNeg) {
      current.path += subtract ? "-" : "+";
      current.path += std::to_string(b);
      current.path += " ";
    }
    if (prev.G < 0 && z.G >= 0) {
      negToNonneg++;
      if (b == 1) b1NegCross++;
      if (subtract) subCross++; else addCross++;
      if (z.q == 2) q2Cross++;
      else if (z.q == 3) q3Cross++;
      else qOtherCross++;
      current.firstB1Cross = n;
      current.recovered = true;
      if (crossingRows.size() < 40) {
        crossingRows.push_back(std::to_string(n) + "," +
          (subtract ? "-" : "+") + "," + std::to_string(b) + "," +
          std::to_string(prev.a) + "," + std::to_string(prev.q) + "," +
          std::to_string(prev.r) + "," + std::to_string(prev.G) + "," +
          std::to_string(z.a) + "," + std::to_string(z.q) + "," +
          std::to_string(z.r) + "," + std::to_string(z.G));
      }
    }
    if (prev.G >= 0 && z.G < 0) nonnegToNeg++;

    if (z.G < 0) {
      if (!inNeg) {
        inNeg = true;
        current = Episode{step, step, 1, z.G, step, z.q, z.q, false};
      } else {
        current.end = step;
        current.length++;
        current.endQ = z.q;
        if (z.G < current.minG) { current.minG = z.G; current.minAt = step; }
      }
    } else if (inNeg) {
      current.end = step - 1;
      episodes.push_back(current);
      if (current.length > maxNegEpisodeLen) {
        maxNegEpisodeLen = current.length;
        maxNegEpisodeStart = current.start;
      }
      inNeg = false;
    }

    prev = z;
  }
  if (inNeg) {
    episodes.push_back(current);
    if (current.length > maxNegEpisodeLen) {
      maxNegEpisodeLen = current.length;
      maxNegEpisodeStart = current.start;
    }
  }

  std::uint64_t epRecovered = 0, epHasB1 = 0, maxDelayFirstB1 = 0,
                maxDelayCross = 0, noB1Complete = 0;
  std::uint64_t longestIdx = 0;
  std::int64_t deepestEpisodeG = 0;
  std::uint64_t deepestEpisodeStart = 0;
  for (std::size_t i = 0; i < episodes.size(); ++i) {
    const auto& e = episodes[i];
    if (e.recovered) epRecovered++;
    if (e.firstB1 != std::numeric_limits<std::uint64_t>::max()) {
      epHasB1++;
      maxDelayFirstB1 = std::max(maxDelayFirstB1, e.firstB1 - e.start);
    } else if (e.recovered) noB1Complete++;
    if (e.firstB1Cross != std::numeric_limits<std::uint64_t>::max())
      maxDelayCross = std::max(maxDelayCross, e.firstB1Cross + 1 - e.start);
    if (e.length == maxNegEpisodeLen) longestIdx = i;
    if (e.minG < deepestEpisodeG) {
      deepestEpisodeG = e.minG; deepestEpisodeStart = e.start;
    }
  }

  std::cout << "N=" << N << " maxA=" << maxA << " distinctA=" << distinctA << " bitsetMB="
            << std::fixed << std::setprecision(2)
            << seen.words.size() * 8.0 / 1024 / 1024 << "\n";
  std::cout << "maxQ=" << maxQ << " at=" << maxQAt
            << " minG=" << minG << " at=" << minGAt
            << " maxG=" << maxG << " at=" << maxGAt << "\n";
  std::cout << "states negative=" << negativeStates
            << " nonnegative=" << nonnegativeStates << "\n";
  std::cout << "borrow_counts";
  for (const auto& [b,c] : bCount) std::cout << " b" << b << "=" << c;
  std::cout << " maxB=" << maxB << " at=" << maxBAt << "\n";
  std::cout << "crossings neg_to_nonneg=" << negToNonneg
            << " b1=" << b1NegCross << " add=" << addCross
            << " sub=" << subCross << " land_q2=" << q2Cross
            << " land_q3=" << q3Cross << " other=" << qOtherCross << "\n";
  std::cout << "nonneg_to_neg=" << nonnegToNeg
            << " b1_from_negative=" << b1NegTransitions << "\n";
  std::cout << "negative_episodes=" << episodes.size()
            << " recovered=" << epRecovered << " has_b1=" << epHasB1
            << " no_b1_complete=" << noB1Complete
            << " max_len=" << maxNegEpisodeLen
            << " max_len_start=" << maxNegEpisodeStart
            << " max_delay_first_b1=" << maxDelayFirstB1
            << " max_delay_cross=" << maxDelayCross
            << " deepest_episode_G=" << deepestEpisodeG
            << " deepest_episode_start=" << deepestEpisodeStart << "\n";
  if (!episodes.empty()) {
    const auto& e = episodes[longestIdx];
    std::cout << "longest_episode start=" << e.start << " end=" << e.end
              << " len=" << e.length << " minG=" << e.minG
              << " minAt=" << e.minAt << " q=" << e.startQ << "->"
              << e.endQ << " firstB1=";
    if (e.firstB1 == std::numeric_limits<std::uint64_t>::max()) std::cout << "none";
    else std::cout << e.firstB1;
    std::cout << " cross=";
    if (e.firstB1Cross == std::numeric_limits<std::uint64_t>::max()) std::cout << "none";
    else std::cout << e.firstB1Cross;
    std::cout << "\n";
  }
  std::cout << "target_states q2_nonneg=" << q2Nonneg
            << " q2_fresh_m=" << q2FreshM << " q2_gate_fresh=" << q2FreshBoth
            << " q3_nonneg=" << q3Nonneg << " q3_fresh_m=" << q3FreshM << "\n";
  std::cout << "target_descent_by_q q:total/fresh/success/freshSuccess";
  for (const auto& [q,c] : targetTotal)
    std::cout << " q" << q << ":" << c << "/" << targetFresh[q]
              << "/" << targetSuccess[q] << "/" << targetFreshSuccess[q];
  std::cout << "\n";
  std::cout << "exact_gate_distinct_m=" << distinctGateMCount
            << " max_m=" << maxGateM << "\n";
  std::cout << "distinct_target_levels allPositiveQ=" << allLevelCount
            << " q1=" << q1LevelCount
            << " q2=" << q2LevelCount << " q3=" << q3LevelCount << "\n";
  std::cout << "first_actual_missing";
  for (std::uint64_t x = 0, found = 0; found < 20; ++x) {
    if (!seen.get(x)) { std::cout << " " << x; found++; }
  }
  std::cout << "\nfirst_q1_level_missing";
  for (std::uint64_t x = 0, found = 0; found < 20; ++x) {
    if (!q1Levels.get(x)) { std::cout << " " << x; found++; }
  }
  std::cout << "\nfirst_any_positive_q_level_missing";
  for (std::uint64_t x = 0, found = 0; found < 20; ++x) {
    if (!allLevels.get(x)) { std::cout << " " << x; found++; }
  }
  std::cout << "\n";
  std::cout << "q_counts";
  for (const auto& [q,c] : qCount) std::cout << " q" << q << "=" << c;
  std::cout << "\n";
  std::cout << "crossing_rows n,branch,b,a,q,r,G,nextA,nextQ,nextR,nextG\n";
  for (const auto& row : crossingRows) std::cout << row << "\n";
  std::cout << "first_b1_rows episodeStart,n,branch,q,r,G,nextQ,nextR,nextG\n";
  for (const auto& row : firstBRows) std::cout << row << "\n";
  std::cout << "episode_rows start,end,len,minG,minAt,startQ,endQ,firstB1,cross,path\n";
  for (const auto& e : episodes) {
    std::cout << e.start << "," << e.end << "," << e.length << ","
              << e.minG << "," << e.minAt << "," << e.startQ << ","
              << e.endQ << ",";
    if (e.firstB1 == std::numeric_limits<std::uint64_t>::max()) std::cout << "none";
    else std::cout << e.firstB1;
    std::cout << ",";
    if (e.firstB1Cross == std::numeric_limits<std::uint64_t>::max()) std::cout << "none";
    else std::cout << e.firstB1Cross;
    std::cout << "," << e.path << "\n";
  }
  std::cout << "gate_rows u,m,a,intermediate\n";
  for (const auto& row : gateRows) std::cout << row << "\n";
  std::cout << "target_watch_rows m=" << watchM
            << " start,q,freshness,outcome,failAt,blockerY\n";
  for (const auto& row : target852Rows) std::cout << row << "\n";
}
