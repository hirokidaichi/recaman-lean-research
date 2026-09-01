#!/usr/bin/env ruby

# Exact greedy continuation of the finite history used to refute the local
# fixed-history-preload route to reset repayment.  The seed is not claimed to
# be reachable from the canonical initial state.

steps = Integer(ARGV.fetch(0, "300"))
target = 4
next_clock = 7
value = 13
seen = {0 => true, 1 => true, 6 => true, 8 => true, 13 => true}
origin = {}

mex = 0
mex += 1 while seen[mex]
active = nil
previous = nil
last_non_high = nil

puts "seeded-preload-counterexample target=#{target} current=#{value} " \
     "nextClock=#{next_clock} steps=#{steps} seen={#{seen.keys.sort.join(',')}}"

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

  unless seen[next_value]
    origin[next_value] = {
      time: clock,
      branch: subtraction ? "sub" : "add",
      predecessor: value
    }
  end
  value = next_value
  seen[value] = true
  mex += 1 while seen[mex]

  if completed && old_mex == target
    reset = previous && completed[:exact_gap] &&
      previous[:blocker] < completed[:blocker]
    blocker_origin = origin[completed[:blocker]]
    origin_text = if blocker_origin
      "#{blocker_origin[:branch]}@#{blocker_origin[:time]}" \
        "(#{blocker_origin[:predecessor]})"
    else
      "seed"
    end
    puts "  terminal start=#{completed[:start]} finish=#{completed[:finish]} " \
         "entry=#{completed[:entry]} blocker=#{completed[:blocker]} " \
         "blockerOrigin=#{origin_text}" \
         "#{reset ? ' UPWARD' : ''}"
    previous = completed
  end

  if old_mex == target && mex != old_mex
    puts "  target-hit clock=#{clock} value=#{value}"
    active = nil
    previous = nil
    last_non_high = nil
  elsif active && mex != old_mex
    active = nil
  end

  raw_candidate = value > clock + 1 ? value - (clock + 1) : 0
  if !active && subtraction && mex == old_mex && value > mex &&
      raw_candidate < mex
    exact_gap = previous &&
      (last_non_high.nil? || last_non_high <= previous[:final_low])
    active = {
      start: clock,
      entry: value,
      landing: value,
      phase: :add,
      exact_gap: exact_gap
    }
  end
  last_non_high = clock if raw_candidate <= mex
end
