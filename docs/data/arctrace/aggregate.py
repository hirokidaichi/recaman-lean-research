#!/usr/bin/env python3
"""Aggregate the arc_trace_probe output of one run directory.

Usage: aggregate.py RUNDIR
Prints a Markdown fragment: deep-arc list, answers (a)-(d) with counts, and
<=80-line excerpts of the traces of the three deepest arcs.
"""
import collections
import math
import os
import sys


def parse_arcs_all(path):
    arcs = []
    with open(path) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            t = line.split()
            arcs.append(dict(
                ordinal=int(t[0]), start=int(t[1]), end=int(t[2]),
                start_value=int(t[3]), index=int(t[4]), value=int(t[5]),
                depth=float(t[6]), late_total=int(t[7]), late_deep=int(t[8]),
                last_late_clock=int(t[9]), last_late_value=int(t[10]),
                trace_from=int(t[11]), trace_len=int(t[12]),
                k0=int(t[13]), k1=int(t[14]), k2=int(t[15]), k3=int(t[16]),
                next_value=int(t[17]), deep=(t[18] == "DEEP")))
    return arcs


def parse_deep(path):
    """Returns {landing_index: dict(header=..., end=[lines], next=line)}."""
    out = {}
    cur = None
    with open(path) as f:
        for line in f:
            if line.startswith("#"):
                continue
            if line.startswith("arc "):
                fields = dict(kv.split("=", 1) for kv in line.split()[2:])
                idx = int(fields["landing"].split("=")[0])
                cur = dict(header=line.rstrip(), fields=fields, end=[], next=None)
                out[idx] = cur
            elif line.startswith("  end "):
                cur["end"].append(line[6:].rstrip())
            elif line.startswith("  next "):
                cur["next"] = line[7:].rstrip()
    return out


def parse_lates(path):
    lates = []
    with open(path) as f:
        for line in f:
            if line.startswith("#"):
                continue
            t = line.split()
            d = dict(clock=int(t[0]), value=int(t[1]), mod3=int(t[2]),
                     below=t[3])
            for kv in t[4:]:
                key, val = kv.split("=", 1)
                d[key] = val
            items = [x for x in d["next8"].split(",") if x]
            d["next_values"] = []
            d["next_types"] = ""
            d["arc_end_in_8"] = False
            for it in items:
                if it == "|arcEnd":
                    d["arc_end_in_8"] = True
                    continue
                v, ty = it.split(":")
                d["next_values"].append(int(v))
                d["next_types"] += ty
            lates.append(d)
    return lates


def read_trace(path):
    header = []
    recs = []
    next_line = None
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("# next arc starts:"):
                next_line = line
            elif line.startswith("#"):
                header.append(line)
            else:
                recs.append(line)
    return header, recs, next_line


def rec_fields(line):
    t = line.split()
    if line.startswith("..."):
        return None
    return dict(clock=int(t[0]), a=int(t[1]), h=int(t[2]), k=int(t[3]),
                r=int(t[4]), step=t[5], cand=t[6], cand_state=t[7],
                cls=t[8], rest=" ".join(t[9:]))


def compress_runs(lates):
    """Groups traced late landings into comb runs: consecutive entries with
    value decreasing by 1 and clock increasing by 2."""
    runs = []
    for d in lates:
        if runs and d["clock"] == runs[-1]["last_clock"] + 2 and \
                d["value"] == runs[-1]["last_value"] - 1:
            runs[-1]["last_clock"] = d["clock"]
            runs[-1]["last_value"] = d["value"]
            runs[-1]["n"] += 1
        else:
            runs.append(dict(first_clock=d["clock"], first_value=d["value"],
                             last_clock=d["clock"], last_value=d["value"], n=1))
    return runs


def excerpt(header, recs, next_line, landing_clock, limit=80):
    lines = list(header)
    body = recs
    if len(body) + len(lines) + 1 <= limit:
        lines.extend(body)
        lines.append(next_line)
        return lines
    # locate the landing record
    li = None
    for i, line in enumerate(body):
        f = rec_fields(line)
        if f and f["clock"] == landing_clock:
            li = i
            break
    head_n, before, after, tail_n = 5, 24, 30, 14
    budget = limit - len(lines) - 1  # for next_line
    chosen = []
    if li is None:
        chosen = body[:head_n] + ["..."] + body[-(budget - head_n - 1):]
    else:
        lo = max(0, li - before)
        hi = min(len(body), li + after + 1)
        parts = []
        if lo > head_n:
            parts.extend(body[:head_n])
            parts.append("... %d records omitted ..." % (lo - head_n))
        else:
            lo = 0
        parts.extend(body[lo:hi])
        if hi < len(body) - tail_n:
            parts.append("... %d records omitted ..." % (len(body) - tail_n - hi))
            parts.extend(body[-tail_n:])
        else:
            parts.extend(body[hi:])
        chosen = parts
        while len(chosen) > budget:
            # trim from the 'before' side first
            chosen.pop(len(header) and 6 if len(chosen) > 8 else 0)
    lines.extend(chosen)
    lines.append(next_line)
    return lines[:limit]


def main():
    rundir = sys.argv[1]
    arcs = parse_arcs_all(os.path.join(rundir, "arcs_all.txt"))
    deep = parse_deep(os.path.join(rundir, "deep_arcs.txt"))
    deep_arcs = [a for a in arcs if a["deep"]]
    print("## Deep arcs (landing value * 10000 < landing index): %d of %d completed arcs"
          % (len(deep_arcs), len(arcs)))
    print()
    print("| arc | clocks | landing index | value | depth log10(i/v) | late landings in arc | late landings traced (r<n/1000) | traced clocks (k0/k1/k2/k3+) | steps after landing | end |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    end_reasons = collections.Counter()
    per_arc = {}
    for a in deep_arcs:
        idx = a["index"]
        d = deep[idx]
        lates = parse_lates(os.path.join(rundir, "lates_%d.txt" % idx))
        header, recs, next_line = read_trace(os.path.join(rundir, "trace_%d.txt" % idx))
        # end classification: the last traced late landing == the arc landing
        last = lates[-1]
        assert last["clock"] == idx and last["value"] == a["value"], (last, a)
        nt = last["next_types"]
        after_landing = a["end"] - idx
        # what follows the landing
        if nt.startswith("AL"):
            first = "comb continues (impossible for the last late)"
        elif nt.startswith("AAB"):
            first = "v-1 visited, band value landed at +3"
        elif nt.startswith("AAA"):
            first = "v-1 visited, band value blocked: pop-up to k=3 at +3"
        else:
            first = "pattern " + nt
        # the end records
        endf = [rec_fields(x) for x in d["end"]]
        nextf = rec_fields(d["next"])
        last_rec = endf[-1]
        last_sub = None
        for f in reversed(endf):
            if f["step"] == "S":
                last_sub = f
                break
        tail_steps = "".join(f["step"] for f in endf[-8:])
        tail_k = ",".join(str(f["k"]) for f in endf[-8:])
        reason = "wrap at k=%d r=%d after steps %s (k: %s); next arc a=%d (k=%d r=%d)" % (
            last_rec["k"], last_rec["r"], tail_steps, tail_k, nextf["a"], nextf["k"], nextf["r"])
        end_reasons[(nt[:3], last_rec["k"])] += 1
        per_arc[idx] = dict(arc=a, lates=lates, header=header, recs=recs,
                            next_line=next_line, first=first, reason=reason,
                            endf=endf, nextf=nextf)
        print("| %d | %d..%d | %d | %d | %.3f | %d | %d | %d/%d/%d/%d | %d | after landing: %s; %s |" % (
            a["ordinal"], a["start"], a["end"], idx, a["value"], a["depth"],
            a["late_total"], a["late_deep"], a["k0"], a["k1"], a["k2"], a["k3"],
            after_landing, first, reason))
    print()

    # (a) next 8 after each traced late landing
    print("## (a) Next 8 orbit values after each traced late landing")
    print()
    pat = collections.Counter()
    n_lates = 0
    for idx, p in per_arc.items():
        for d in p["lates"]:
            n_lates += 1
            pat[d["next_types"] + ("|end" if d["arc_end_in_8"] else "")] += 1
    print("Traced late landings over all deep arcs: %d. Step-type pattern of the next 8 clocks"
          " (A = addition, B = subtraction landing a value >= clock, L = subtraction landing"
          " a value < clock = late landing):" % n_lates)
    print()
    print("| pattern | count |")
    print("|---|---|")
    for k, v in pat.most_common():
        print("| %s | %d |" % (k, v))
    print()
    # explicit values for the landing (last late) of each deep arc
    print("Values after the arc landing itself (the last late landing of each deep arc), v = landing value, c = landing clock:")
    print()
    print("| landing | next 8 values | types |")
    print("|---|---|---|")
    for idx, p in per_arc.items():
        d = p["lates"][-1]
        print("| %d=%d | %s | %s |" % (idx, d["value"], ", ".join(str(x) for x in d["next_values"]), d["next_types"]))
    print()

    # (b) small-height continuation
    print("## (b) Later clock in the same arc with 0 < h < v after a late landing at v")
    print()
    res = collections.Counter()
    off = collections.Counter()
    for idx, p in per_arc.items():
        for d in p["lates"]:
            if d["small"] == "none":
                res["none"] += 1
            else:
                sc, sh = d["small"].split(":")
                sc, sh = int(sc), int(sh)
                o = sc - d["clock"]
                dv = d["value"] - sh
                res["found"] += 1
                off[(o, "h=v-%d" % dv if dv <= 3 else "h=v-%d" % dv)] += 1
    print("found: %d, none: %d" % (res["found"], res["none"]))
    print()
    print("| clock offset of first later clock with 0<h<v | h relative to v | count |")
    print("|---|---|---|")
    for (o, rel), c in sorted(off.items(), key=lambda kv: (-kv[1], kv[0])):
        print("| +%d | %s | %d |" % (o, rel, c))
    print()
    print("Height at +2 after each traced late landing (value at +2 relative to clock):")
    two = collections.Counter()
    for idx, p in per_arc.items():
        for d in p["lates"]:
            if len(d["next_values"]) >= 2:
                v2 = d["next_values"][1]
                c2 = d["clock"] + 2
                h2 = v2 - c2
                if h2 < 0:
                    two["+2 is a late landing (h<0): comb continues"] += 1
                else:
                    kk = v2 // c2
                    two["+2 has k=%d (h = %s)" % (kk, "clock+v-1" if v2 == 2 * c2 + d["value"] - 1 else "other")] += 1
    for k, v in two.most_common():
        print("- %s: %d" % (k, v))
    print()

    # (c) end reasons
    print("## (c) How each deep arc ends")
    print()
    for idx, p in per_arc.items():
        a = p["arc"]
        print("- arc %d (landing %d=%d): %d steps after the landing; after the landing: %s; %s" % (
            a["ordinal"], idx, a["value"], a["end"] - idx, p["first"], p["reason"]))
    print()
    print("Counts by (first three step types after the landing, k at the wrap): %s" % dict(end_reasons))
    print()
    # last subtraction of each deep arc
    print("Last 16 records of each deep arc (clock a h k r step cand candState class ...):")
    print()
    for idx, p in per_arc.items():
        print("arc landing %d=%d" % (idx, p["arc"]["value"]))
        print()
        print("```")
        for line in deep[idx]["end"]:
            print(line)
        print("next: " + deep[idx]["next"])
        print("```")
        print()

    # (d) late-landing values per deep arc
    print("## (d) Traced late-landing values per deep arc with residues mod 3")
    print()
    for idx, p in per_arc.items():
        lates = p["lates"]
        runs = compress_runs(lates)
        print("arc landing %d=%d: %d traced late landings in %d comb runs (a run = values decreasing by 1 every 2 clocks)" % (
            idx, p["arc"]["value"], len(lates), len(runs)))
        print()
        print("| run | clocks | values | count | value mod 3 (first..last) | below-hole at first landing |")
        print("|---|---|---|---|---|---|")
        by_clock = {d["clock"]: d for d in lates}
        for i, r in enumerate(runs):
            first = by_clock[r["first_clock"]]
            if r["n"] == 1:
                vals = str(r["first_value"])
                mods = str(r["first_value"] % 3)
            else:
                vals = "%d..%d" % (r["first_value"], r["last_value"])
                mods = "%d..%d" % (r["first_value"] % 3, r["last_value"] % 3)
            clocks = str(r["first_clock"]) if r["n"] == 1 else "%d..%d" % (r["first_clock"], r["last_clock"])
            print("| %d | %s | %s | %d | %s | %s |" % (i + 1, clocks, vals, r["n"], mods, first["below"]))
        print()
        # residues of consecutive run-first values
        firsts = [r["first_value"] for r in runs]
        print("Run-first values mod 3: %s" % ",".join(str(v % 3) for v in firsts))
        print("Differences between consecutive run-first values mod 3: %s" % ",".join(
            str((firsts[i] - firsts[i + 1]) % 3) for i in range(len(firsts) - 1)))
        print("Mod-3 distribution of all traced late-landing values: %s" % dict(collections.Counter(d["mod3"] for d in lates)))
        print("below-hole at traced late landings: %s" % dict(collections.Counter(d["below"] for d in lates)))
        print()

    # excerpts of the three deepest arcs
    deepest = sorted(per_arc.values(), key=lambda p: -p["arc"]["depth"])[:3]
    print("## Example traces (three deepest arcs, at most 80 lines each)")
    print()
    print("Columns: clock a h k r step cand candState class [mod3= below=] [UP] [POP]."
          " k = floor(a/clock), r = a mod clock; UP = k>=2 right after a record with k<=1;"
          " POP = k>=3.")
    print()
    for p in deepest:
        a = p["arc"]
        print("### arc %d, landing %d=%d, depth %.3f" % (a["ordinal"], a["index"], a["value"], a["depth"]))
        print()
        print("```")
        for line in excerpt(p["header"], p["recs"], p["next_line"], a["index"]):
            print(line)
        print("```")
        print()


if __name__ == "__main__":
    main()
