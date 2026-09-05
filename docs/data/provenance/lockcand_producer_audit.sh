#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 RECORDS DISCOVERY_CUTOFF" >&2
  exit 2
fi

records=$1
cutoff=$2

awk -v cutoff="$cutoff" '
function split_name(c) { return c < cutoff ? "discovery" : "holdout" }
function step_word(w, am2, am1, step, ap1, ap2) {
  return (am1 > am2 ? "A" : "S") step (ap1 > w ? "A" : "S") (ap2 > ap1 ? "A" : "S")
}
function remember_violation(reason, line) {
  violations[reason]++
  if (shown < 20) {
    bad[++shown] = reason ": " line
  }
}
BEGIN {
  names[1] = "same-upper"
  names[2] = "same-lower"
  names[3] = "same-both"
  names[4] = "same-ladder"
  names[5] = "same-valley"
  names[6] = "prev-ladder"
  splits[1] = "discovery"
  splits[2] = "holdout"
  words[1] = "AAAA"
  words[2] = "AAAS"
  words[3] = "AASA"
  words[4] = "AASS"
  words[5] = "ASAA"
  words[6] = "ASAS"
  words[7] = "ASSA"
  words[8] = "ASSS"
  words[9] = "SAAA"
  words[10] = "SAAS"
  words[11] = "SASA"
  words[12] = "SASS"
  words[13] = "SSAA"
  words[14] = "SSAS"
  words[15] = "SSSA"
  words[16] = "SSSS"
}
$1 == "lockcand" && NF >= 26 {
  s = split_name($3)
  w = $2 + 0
  c = $3 + 0
  n = $12 + 0
  q = $14 + 0
  arc_c = $6 + 0
  arc_n = $16 + 0
  upper = $22 + 0
  lower = $23 + 0
  same = $24 + 0
  pattern = step_word(w, $18 + 0, $19 + 0, $13, $20 + 0, $21 + 0)
  recomputed_upper = (($21 + 0 == w + 1) || ($18 + 1 == w))
  recomputed_lower = (($21 + 1 == w) || ($18 + 0 == w + 1))
  v = $4 + 0
  k = $8 + 0
  r = $15 + 0

  total[s]++
  if (n < 2 || n >= c) remember_violation(s "/time", $0)
  if (13 + 7 * k > v) remember_violation(s "/budget", $0)
  if (w != 2 * c + v - 1 - 3 * k) remember_violation(s "/formula", $0)
  if (upper != recomputed_upper || lower != recomputed_lower)
    remember_violation(s "/flag", $0)
  if (same != (arc_n == arc_c)) remember_violation(s "/same-arc-flag", $0)
  if (same && q == 2 &&
      (2 * (c - n) + 12 + 4 * k > r || 2 * (c - n) + 13 + 4 * k > n))
    remember_violation(s "/gap-cost", $0)

  producer_count[w SUBSEP n]++
  arc_count[s SUBSEP arc_c]++

  class = ""
  if (same && q == 2) {
    if (upper && !lower) class = "same-upper"
    else if (!upper && lower) class = "same-lower"
    else if (upper && lower) class = "same-both"
    else if (pattern == "SSSS") class = "same-ladder"
    else if (pattern == "SSAA") class = "same-valley"
  } else if (!same && arc_n + 1 == arc_c && q == 4 && !upper && !lower && pattern == "SSSS") {
    class = "prev-ladder"
  }

  if (class == "") {
    remember_violation(s "/classification", $0)
    unknown[s, pattern, q, arc_c - arc_n, upper, lower]++
  } else {
    count[s, class]++
  }
  patterns[s, pattern]++
}
END {
  print "lockcand producer audit"
  print "discovery cutoff c < " cutoff
  for (si = 1; si <= 2; ++si) {
    s = splits[si]
    print "[" s "] total=" (total[s] + 0)
    for (i = 1; i <= 6; ++i) {
      name = names[i]
      print "  " name "=" (count[s, name] + 0)
    }
    printf "  patterns:"
    for (i = 1; i <= 16; ++i)
      if (patterns[s, words[i]] > 0) printf " %s=%d", words[i], patterns[s, words[i]]
    print ""
  }
  print "violations:"
  violation_total = 0
  for (v in violations) violation_total += violations[v]
  print "  total=" violation_total
  for (v in violations) print "  " v "=" violations[v]
  if (shown > 0) {
    print "first violations:"
    for (i = 1; i <= shown; ++i) print "  " bad[i]
  }
  distinct_producers = 0
  max_producer_charge = 0
  for (key in producer_count) {
    distinct_producers++
    if (producer_count[key] > max_producer_charge) max_producer_charge = producer_count[key]
  }
  print "charge diagnostics:"
  print "  distinct (w,n) producers=" distinct_producers
  print "  maximum queries per (w,n) producer=" max_producer_charge
  for (si = 1; si <= 2; ++si) {
    s = splits[si]
    max_arc_charge = 0
    for (key in arc_count) {
      split(key, parts, SUBSEP)
      if (parts[1] == s && arc_count[key] > max_arc_charge) max_arc_charge = arc_count[key]
    }
    print "  " s " maximum lockcand queries per event arc=" max_arc_charge
  }
  exit violation_total == 0 ? 0 : 1
}
' "$records"
