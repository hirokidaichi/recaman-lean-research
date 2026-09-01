#!/usr/bin/env ruby

# Falsification harness for non-uniform upward-reset repayment.
#
# Each sample starts from a reproducible nonnegative signed-clock seed, then
# follows the exact greedy Recaman rule.  The seed is deliberately not claimed
# to be reachable from the canonical initial state.  It tests which candidate
# repayment laws follow from local step legality and target-low macro gates,
# not the exact permanent-missing hypothesis.

seed_count = Integer(ARGV.fetch(0, "5000"))
maximum_next_clock = Integer(ARGV.fetch(1, "200"))
steps = Integer(ARGV.fetch(2, "10000"))
random_seed = Integer(ARGV.fetch(3, "20260901"))
rng = Random.new(random_seed)

stats = Hash.new(0)
examples = []

seed_count.times do |sample|
  next_clock = rng.rand(3..maximum_next_clock)
  seen = {0 => true}
  value = 0
  (1...next_clock).each do |clock|
    if value > clock && rng.rand(2) == 1
      value -= clock
    else
      value += clock
    end
    seen[value] = true
  end

  mex = 0
  mex += 1 while seen[mex]
  active = nil
  previous = nil
  pending = []
  last_non_high = nil

  steps.times do |offset|
    clock = next_clock + offset
    candidate = value - clock
    subtraction = value > clock && !seen[candidate]
    next_value = subtraction ? candidate : value + clock
    old_mex = mex
    completed = nil

    if active
      if active[:phase] == :add
        if subtraction
          active = nil
        else
          active[:phase] = :resolve
        end
      elsif subtraction
        if next_value + 1 != active[:landing]
          active = nil
        else
          active[:landing] = next_value
          active[:phase] = :add
        end
      else
        completed = {
          target: active[:target],
          start: active[:start],
          finish: clock,
          final_low: clock - 2,
          entry: active[:entry],
          blocker: active[:landing] - 1,
          exact_gap: active[:exact_gap]
        }
        active = nil
      end
    end

    if completed
      pending.each do |reset|
        reset[:later_terminals] += 1
        next unless completed[:start] > reset[:final_low] &&
                    completed[:entry] < reset[:anchor]

        reset[:repaid] = true
        stats[:repaid] += 1
        stats[:maximum_repay_wait] = [
          stats[:maximum_repay_wait], reset[:later_terminals]
        ].max
      end
      pending.reject! { |reset| reset[:repaid] }

      if previous && completed[:exact_gap] &&
          previous[:blocker] < completed[:blocker]
        stats[:upward_macro] += 1
        pending << {
          anchor: completed[:blocker],
          final_low: completed[:final_low],
          sample: sample,
          target: completed[:target],
          source_start: completed[:start],
          later_terminals: 0
        }
      end
      previous = completed
    end

    value = next_value
    seen[value] = true
    mex += 1 while seen[mex]

    if active && mex != old_mex
      active = nil
    end
    if mex != old_mex
      stats[:target_ended] += pending.length
      pending.each do |reset|
        if examples.length < 4
          examples << reset.merge(outcome: "target-ended", hit_clock: clock)
        end
      end
      pending.clear
      previous = nil
      last_non_high = nil
    end

    raw_candidate = value > clock + 1 ? value - (clock + 1) : 0
    if !active && subtraction && mex == old_mex && value > mex &&
        raw_candidate < mex
      exact_gap = previous &&
        (last_non_high.nil? || last_non_high <= previous[:final_low])
      active = {
        target: mex,
        start: clock,
        entry: value,
        landing: value,
        phase: :add,
        exact_gap: exact_gap
      }
    end
    last_non_high = clock if raw_candidate <= mex
  end

  stats[:censored] += pending.length
  pending.each do |reset|
    age = next_clock + steps - 1 - reset[:source_start]
    stats[:maximum_censor_age] = [stats[:maximum_censor_age], age].max
    stats[:maximum_censor_later] = [
      stats[:maximum_censor_later], reset[:later_terminals]
    ].max
    stats[:mature_censored] += 1 if age >= steps / 2
    examples << reset.merge(outcome: "censored") if examples.length < 4
  end
end

puts "seeded-repayment-holdout seeds=#{seed_count} " \
     "maxNextClock=#{maximum_next_clock} steps=#{steps} rng=#{random_seed}"
puts "  exactMacroUpward=#{stats[:upward_macro]} " \
     "repaid=#{stats[:repaid]} targetEnded=#{stats[:target_ended]} " \
     "censored=#{stats[:censored]}"
puts "  maximumRepayWaitEpisodes=#{stats[:maximum_repay_wait]} " \
     "matureCensored=#{stats[:mature_censored]} " \
     "maximumCensorAge=#{stats[:maximum_censor_age]} " \
     "maximumCensorLaterEpisodes=#{stats[:maximum_censor_later]}"
examples.each do |example|
  line = "  #{example[:outcome]} sample=#{example[:sample]} " \
         "target=#{example[:target]} sourceStart=#{example[:source_start]} " \
         "anchor=#{example[:anchor]}"
  line += " hitClock=#{example[:hit_clock]}" if example[:hit_clock]
  puts line
end
