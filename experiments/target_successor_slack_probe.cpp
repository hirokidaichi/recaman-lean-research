// Numerical slack audit for immediate same-target history-terminal macros.

#define main target_comb_extraction_embedded_main
#include "target_comb_extraction_probe.cpp"
#undef main

#include <cmath>
#include <iomanip>
#include <string>

namespace {

struct EdgeSample {
  Value target = 0U;
  Clock previous_start = 0U;
  Clock next_start = 0U;
  Value previous_entry = 0U;
  Value next_entry = 0U;
  Value next_blocker = 0U;
  Value absolute_slack = 0U;
  Value next_mass = 0U;
  Value high_clocks = 0U;
  Value exit_excess = 0U;
  Value low_deficit = 0U;
  bool upward = false;
};

Value PercentileValue(std::vector<Value> values, std::size_t percentile) {
  if (values.empty()) return 0U;
  std::sort(values.begin(), values.end());
  const std::size_t index = std::min(
      values.size() - 1U, values.size() * percentile / 100U);
  return values[index];
}

double Correlation(const std::vector<EdgeSample>& samples,
                   Value EdgeSample::*left, Value EdgeSample::*right) {
  if (samples.size() < 2U) return 0.0;
  long double sum_left = 0.0L, sum_right = 0.0L;
  for (const EdgeSample& sample : samples) {
    sum_left += static_cast<long double>(sample.*left);
    sum_right += static_cast<long double>(sample.*right);
  }
  const long double mean_left = sum_left / samples.size();
  const long double mean_right = sum_right / samples.size();
  long double covariance = 0.0L, variance_left = 0.0L;
  long double variance_right = 0.0L;
  for (const EdgeSample& sample : samples) {
    const long double x = static_cast<long double>(sample.*left) - mean_left;
    const long double y = static_cast<long double>(sample.*right) - mean_right;
    covariance += x * y;
    variance_left += x * x;
    variance_right += y * y;
  }
  if (variance_left == 0.0L || variance_right == 0.0L) return 0.0;
  return static_cast<double>(
      covariance / std::sqrt(variance_left * variance_right));
}

void PrintGroup(const char* label, const std::vector<EdgeSample>& samples) {
  std::vector<Value> slack, mass, clocks, excess, deficit;
  Count equality = 0U, odd_slack = 0U;
  Count even_slack_ge_mass = 0U, parity_mass_gate_failures = 0U;
  Count slack_ge_mass = 0U, slack_ge_clocks = 0U;
  Count slack_ge_deficit = 0U;
  EdgeSample minimum;
  bool have_minimum = false;
  for (const EdgeSample& sample : samples) {
    slack.push_back(sample.absolute_slack);
    mass.push_back(sample.next_mass);
    clocks.push_back(sample.high_clocks);
    excess.push_back(sample.exit_excess);
    deficit.push_back(sample.low_deficit);
    if (sample.absolute_slack == 0U) ++equality;
    if ((sample.absolute_slack & 1U) != 0U) ++odd_slack;
    if ((sample.absolute_slack & 1U) == 0U &&
        sample.next_mass <= sample.absolute_slack)
      ++even_slack_ge_mass;
    if ((sample.absolute_slack & 1U) == 0U &&
        sample.absolute_slack < sample.next_mass)
      ++parity_mass_gate_failures;
    if (sample.next_mass <= sample.absolute_slack) ++slack_ge_mass;
    if (sample.high_clocks <= sample.absolute_slack) ++slack_ge_clocks;
    if (sample.low_deficit <= sample.absolute_slack) ++slack_ge_deficit;
    if (!have_minimum || sample.absolute_slack < minimum.absolute_slack) {
      have_minimum = true;
      minimum = sample;
    }
  }
  std::cout << "  " << label << " edges=" << samples.size()
            << " equality=" << equality << " oddSlack=" << odd_slack
            << " evenSlackGeMass=" << even_slack_ge_mass
            << " parityMassGateFailures=" << parity_mass_gate_failures
            << " slack(min/p50/p90/p99/max)="
            << PercentileValue(slack, 0U) << '/'
            << PercentileValue(slack, 50U) << '/'
            << PercentileValue(slack, 90U) << '/'
            << PercentileValue(slack, 99U) << '/'
            << (slack.empty() ? 0U : *std::max_element(slack.begin(), slack.end()))
            << '\n'
            << "    nextMass(p50/p90/max)=" << PercentileValue(mass, 50U)
            << '/' << PercentileValue(mass, 90U) << '/'
            << (mass.empty() ? 0U : *std::max_element(mass.begin(), mass.end()))
            << " highClocks(p50/p90/max)="
            << PercentileValue(clocks, 50U) << '/'
            << PercentileValue(clocks, 90U) << '/'
            << (clocks.empty() ? 0U : *std::max_element(clocks.begin(), clocks.end()))
            << '\n'
            << "    exitExcess(p50/p90/max)="
            << PercentileValue(excess, 50U) << '/'
            << PercentileValue(excess, 90U) << '/'
            << (excess.empty() ? 0U : *std::max_element(excess.begin(), excess.end()))
            << " lowDeficit(p50/p90/max)="
            << PercentileValue(deficit, 50U) << '/'
            << PercentileValue(deficit, 90U) << '/'
            << (deficit.empty() ? 0U : *std::max_element(deficit.begin(), deficit.end()))
            << '\n'
            << "    slack>=mass/clocks/deficit=" << slack_ge_mass << '/'
            << slack_ge_clocks << '/' << slack_ge_deficit
            << " corr(slack,mass/clocks/excess/deficit)=" << std::fixed
            << std::setprecision(4)
            << Correlation(samples, &EdgeSample::absolute_slack,
                           &EdgeSample::next_mass)
            << '/'
              << Correlation(samples, &EdgeSample::absolute_slack,
                           &EdgeSample::high_clocks)
            << '/'
            << Correlation(samples, &EdgeSample::absolute_slack,
                           &EdgeSample::exit_excess)
            << '/'
            << Correlation(samples, &EdgeSample::absolute_slack,
                           &EdgeSample::low_deficit) << '\n';
  if (have_minimum) {
    std::cout << "    minimum witness target=" << minimum.target
              << " previousStart/entry=" << minimum.previous_start << '/'
              << minimum.previous_entry
              << " nextStart/entry/blocker=" << minimum.next_start << '/'
              << minimum.next_entry << '/' << minimum.next_blocker
              << " slack=" << minimum.absolute_slack
              << " nextMass=" << minimum.next_mass
              << " highClocks=" << minimum.high_clocks
              << " exitExcess=" << minimum.exit_excess
              << " lowDeficit=" << minimum.low_deficit << '\n';
  }
}

void AnalyzeSuccessorSlack(Clock horizon, Clock train_cutoff) {
  const RunData data = Generate(horizon);
  std::unordered_map<Value, Episode> previous_by_target;
  std::vector<EdgeSample> all, upward, downward, train_upward, holdout_upward;
  Count parity_identity_violations = 0U;
  Count right_order_violations = 0U, left_order_violations = 0U;
  for (const Episode& episode : data.episodes) {
    if (episode.kind != EpisodeKind::history_terminal) {
      previous_by_target.erase(episode.target);
      continue;
    }
    const auto found = previous_by_target.find(episode.target);
    if (found != previous_by_target.end()) {
      const Episode& previous = found->second;
      const bool is_upward = previous.blocker < episode.blocker;
      const Value slack = episode.blocker < previous.entry
          ? previous.entry - episode.blocker
          : episode.blocker - previous.entry;
      const Value mass = episode.entry - episode.blocker;
      const Clock high_clocks = static_cast<Clock>(
          episode.start - previous.end + 1U);
      const Value exit_excess = episode.entry - episode.target;
      const Value low_line =
          episode.target + static_cast<Value>(episode.start) + 1U;
      const Value low_deficit = low_line - episode.entry;
      const EdgeSample sample{
          episode.target, previous.start, episode.start, previous.entry,
          episode.entry, episode.blocker, slack, mass, high_clocks,
          exit_excess, low_deficit, is_upward};
      all.push_back(sample);
      if (is_upward) {
        upward.push_back(sample);
        if (episode.blocker < previous.entry) ++right_order_violations;
        if (episode.start <= train_cutoff)
          train_upward.push_back(sample);
        else
          holdout_upward.push_back(sample);
      } else {
        downward.push_back(sample);
        if (previous.blocker <= episode.entry) ++left_order_violations;
      }
      const Value entry_difference = episode.entry < previous.entry
          ? previous.entry - episode.entry
          : episode.entry - previous.entry;
      const Value triangular_difference =
          (static_cast<Value>(episode.start) * (episode.start + 1ULL) -
           static_cast<Value>(previous.start) * (previous.start + 1ULL)) /
          2ULL;
      if ((entry_difference & 1ULL) != (triangular_difference & 1ULL))
        ++parity_identity_violations;
    }
    previous_by_target[episode.target] = episode;
  }
  std::cout << "target-successor-slack horizon=" << horizon
            << " trainCutoff=" << train_cutoff
            << " parityIdentityViolations=" << parity_identity_violations
            << " orderViolations(up/down)=" << right_order_violations << '/'
            << left_order_violations << '\n';
  PrintGroup("all", all);
  PrintGroup("upward/right", upward);
  PrintGroup("downward/left", downward);
  PrintGroup("upward train", train_upward);
  PrintGroup("upward holdout", holdout_upward);
  std::cout << "  upward edge details:\n";
  for (const EdgeSample& sample : upward) {
    std::cout << "    target=" << sample.target
              << " starts=" << sample.previous_start << "->"
              << sample.next_start << " previousEntry="
              << sample.previous_entry << " nextEntry/blocker="
              << sample.next_entry << '/' << sample.next_blocker
              << " slack/mass/high/excess/deficit="
              << sample.absolute_slack << '/' << sample.next_mass << '/'
              << sample.high_clocks << '/' << sample.exit_excess << '/'
              << sample.low_deficit << '\n';
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const Clock horizon = argc >= 2 ? ParseClock(argv[1]) : 20000000U;
    const Clock cutoff = argc >= 3 ? ParseClock(argv[2]) : 2000000U;
    AnalyzeSuccessorSlack(horizon, cutoff);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
