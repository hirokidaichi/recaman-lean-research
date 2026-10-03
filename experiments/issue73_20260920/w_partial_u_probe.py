#!/usr/bin/env python3
"""Bounded probe for W with only full-supply completeness removed.

This is a discovery-range experiment, not a proof or a reusable acceptance gate.
It does not import the earlier baseline or falsification gate.
"""

import argparse
import json
import time
from itertools import combinations, product


W1 = "SAAAASS"


class LimitReached(Exception):
    pass


def emit(kind, **payload):
    print(json.dumps({"kind": kind, **payload}, sort_keys=True, separators=(",", ":")), flush=True)


def subsets(items):
    values = tuple(items)
    for size in range(len(values) + 1):
        for choice in combinations(values, size):
            yield choice


def past(word, t, distance):
    period = len(word)
    return "".join(word[(t - offset) % period] for offset in range(1, distance + 1))


def mass(window):
    return sum(1 if bit == "A" else -1 for bit in window)


def moment(window):
    return sum(offset * (1 if bit == "A" else -1) for offset, bit in enumerate(window, 1))


def is_p2(window):
    return mass(window) == 1 and moment(window) == 0


def cover_of_window(word, u, distance):
    period = len(word)
    return tuple(sorted({(u - offset) % period for offset in range(1, distance + 1)
                         if word[(u - offset) % period] == "S"}))


def neighborhood(supply, subset):
    covered = set()
    for u in subset:
        covered.update(supply[u]["cover"])
    return tuple(sorted(covered))


def least_supply(word, u, check_limit):
    period = len(word)
    for distance in range(1, period * (period + 1) + 1):
        check_limit()
        window = past(word, u, distance)
        if is_p2(window):
            return {"lag": distance, "window": window,
                    "cover": cover_of_window(word, u, distance)}
    return None


def full_supply(word, check_limit):
    answer = {}
    for u, bit in enumerate(word):
        check_limit()
        if bit == "A":
            found = least_supply(word, u, check_limit)
            if found is not None:
                answer[u] = found
    return answer


def hall_details(supply, universe, check_limit):
    checks = []
    for subset in subsets(universe):
        check_limit()
        covered = neighborhood(supply, subset)
        checks.append({"subset": list(subset), "neighborhood": list(covered),
                       "lhs": len(subset), "rhs": len(covered)})
        if len(subset) > len(covered):
            return False, checks, checks[-1]
    return True, checks, None


def positive_mass(word):
    return word.count("A") - word.count("S")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-period", type=int, required=True)
    parser.add_argument("--max-work", type=int, required=True)
    parser.add_argument("--seconds", type=float, required=True)
    args = parser.parse_args()
    if args.max_period < 1 or args.max_work < 1 or args.seconds <= 0:
        parser.error("all limits must be positive")

    started = time.monotonic()
    deadline = started + args.seconds
    positive_words = 0
    completed_positive_words = 0
    incomplete_u_examined = 0
    tight_b_examined = 0
    w1_antecedents = 0
    work = 0
    last_period = 0
    last_word = None

    def check_limit():
        if time.monotonic() >= deadline:
            raise LimitReached("seconds")

    emit("meta", max_period=args.max_period, max_work=args.max_work, seconds=args.seconds,
         lag_bound="inclusive 1..p(p+1)", bit_order="word[u], past newest-to-oldest",
         search="all positive-mass words; tight short B; all proper U supersets; representative t")

    try:
        for period in range(1, args.max_period + 1):
            last_period = period
            for bits in product("SA", repeat=period):
                check_limit()
                word = "".join(bits)
                last_word = word
                if positive_mass(word) <= 0:
                    continue
                positive_words += 1
                supply = full_supply(word, check_limit)
                phases = tuple(sorted(supply))
                short = tuple(u for u in phases if supply[u]["lag"] in (3, 7))

                for b_tuple in subsets(short):
                    check_limit()
                    if not b_tuple:
                        continue
                    b_neighborhood = neighborhood(supply, b_tuple)
                    if len(b_neighborhood) != len(b_tuple):
                        continue
                    tight_b_examined += 1
                    antecedent_t = tuple(t for t in range(period)
                                         if t in b_tuple and supply[t]["lag"] == 7
                                         and past(word, t, 7) == W1)
                    if not antecedent_t:
                        continue
                    optional = tuple(u for u in phases if u not in b_tuple)
                    for extras in subsets(optional):
                        check_limit()
                        u_tuple = tuple(sorted((*b_tuple, *extras)))
                        if len(u_tuple) == len(phases):
                            continue
                        incomplete_u_examined += 1
                        hall_ok, hall_checks, _ = hall_details(supply, u_tuple, check_limit)
                        if not hall_ok:
                            continue
                        for t in antecedent_t:
                            work += 1
                            if work > args.max_work:
                                raise LimitReached("max_work")
                            w1_antecedents += 1
                            if word[(t + 1) % period] != "S":
                                continue
                            missing = tuple(u for u in phases if u not in u_tuple)
                            full_hall, full_checks, full_failure = hall_details(
                                supply, phases, check_limit)
                            full_same_violation = (
                                full_hall and t in phases and supply[t]["lag"] == 7
                                and past(word, t, 7) == W1
                                and word[(t + 1) % period] == "S"
                            )
                            witness = {
                                "period": period,
                                "word": word,
                                "sign_sum": positive_mass(word),
                                "t": t,
                                "phase_t": t % period,
                                "next_bit": word[(t + 1) % period],
                                "past7": past(word, t, 7),
                                "U": list(u_tuple),
                                "B": list(b_tuple),
                                "missing_supply": list(missing),
                                "supply": {str(u): {"lag": item["lag"],
                                                    "window": item["window"],
                                                    "cover": list(item["cover"])}
                                           for u, item in sorted(supply.items())},
                                "N_B": list(b_neighborhood),
                                "hall_U_checks": hall_checks,
                                "full_supply_hall": full_hall,
                                "full_supply_hall_checks": full_checks,
                                "full_supply_hall_failure": full_failure,
                                "full_same_W_violation": full_same_violation,
                            }
                            result = "original_W_candidate" if full_same_violation else "partial_only_candidate"
                            emit("witness", result=result, witness=witness)
                            emit("summary", status="FOUND", result=result,
                                 positive_words=positive_words,
                                 completed_positive_words=completed_positive_words,
                                 incomplete_u_examined=incomplete_u_examined,
                                 tight_b_examined=tight_b_examined,
                                 w1_antecedents=w1_antecedents, work=work,
                                 elapsed_seconds=round(time.monotonic() - started, 6))
                            return 0
                completed_positive_words += 1
        emit("summary", status="EXHAUSTED_ZERO", positive_words=positive_words,
             completed_positive_words=completed_positive_words,
             incomplete_u_examined=incomplete_u_examined,
             tight_b_examined=tight_b_examined, w1_antecedents=w1_antecedents,
             work=work, last_period=last_period, last_word=last_word,
             elapsed_seconds=round(time.monotonic() - started, 6),
             representative_to_all_int="periodicity required; independent audit pending")
        return 0
    except LimitReached as exc:
        emit("summary", status="INCOMPLETE", reason=str(exc),
             positive_words=positive_words,
             completed_positive_words=completed_positive_words,
             incomplete_u_examined=incomplete_u_examined,
             tight_b_examined=tight_b_examined, w1_antecedents=w1_antecedents,
             work=work, last_period=last_period, last_word=last_word,
             elapsed_seconds=round(time.monotonic() - started, 6))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
