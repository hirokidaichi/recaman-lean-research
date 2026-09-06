#!/usr/bin/env python3
"""Exact seeded checks for the affine phase-capacity no-go families."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class State:
    clock: int
    value: int
    step: str

    @property
    def quotient(self) -> int:
        return self.value // self.clock

    @property
    def residue(self) -> int:
        return self.value % self.clock


def capacity(state: State) -> int:
    return state.residue // (2 * state.quotient - 1)


def run_to_wrap(boundary: int, current: int, seed: set[int]) -> list[State]:
    assert 0 in seed and current in seed
    states = [State(boundary, current, "initial")]
    seen = set(seed)
    while True:
        prior = states[-1]
        clock = prior.clock + 1
        candidate = prior.value - clock
        subtract = candidate > 0 and candidate not in seen
        value = candidate if subtract else prior.value + clock
        state = State(clock, value, "S" if subtract else "A")
        seen.add(value)
        states.append(state)
        if state.residue > prior.residue:
            return states


def seed_checks(boundary: int, current: int, seed: set[int]) -> None:
    assert len(seed) <= boundary + 1
    assert max(seed) <= boundary * (boundary + 1) // 2
    assert current % 2 == (boundary * (boundary + 1) // 2) % 2


def lower_fresh_family(multiple: int) -> tuple[list[State], State, State]:
    r = 126 * multiple + 12
    n = 4 * r + 16
    boundary = n - 2
    current = 5 * n + r - 1
    seed = {0, current, 3 * n + r}
    seed.update(2 * n + r - 6 - 3 * j for j in range(18 * multiple + 1))
    seed_checks(boundary, current, seed)
    states = run_to_wrap(boundary, current, seed)
    expected_prefix = [
        (n - 2, 5 * n + r - 1, "initial"),
        (n - 1, 4 * n + r, "S"),
        (n, 5 * n + r, "A"),
        (n + 1, 4 * n + r - 1, "S"),
        (n + 2, 3 * n + r - 3, "S"),
        (n + 3, 4 * n + r, "A"),
    ]
    assert [(s.clock, s.value, s.step) for s in states[:6]] == expected_prefix
    assert states[-1].clock == n + 36 * multiple + 4
    assert states[-1].step == "S"
    old_start = states[0]
    new_start = states[3]
    assert (old_start.quotient, old_start.residue) == (5, r + 9)
    assert (new_start.quotient, new_start.residue) == (4, r - 5)
    assert new_start.clock - old_start.clock == 3
    assert new_start.value - old_start.value == -n
    assert capacity(new_start) - capacity(old_start) == 4 * multiple - 1
    return states, old_start, new_start


def upper_blocked_family(n: int = 1024) -> tuple[list[State], State, State]:
    assert n % 4 == 0
    r = 42
    boundary = n - 2
    current = 4 * n + r - 1
    seed = {0, current, 2 * n + r, 3 * n + r - 1}
    seed.update(4 * n + r - 4 - 3 * j for j in range(4))
    seed_checks(boundary, current, seed)
    states = run_to_wrap(boundary, current, seed)
    expected_prefix = [
        (n - 2, 4 * n + r - 1, "initial"),
        (n - 1, 3 * n + r, "S"),
        (n, 4 * n + r, "A"),
        (n + 1, 5 * n + r + 1, "A"),
        (n + 2, 6 * n + r + 3, "A"),
    ]
    assert [(s.clock, s.value, s.step) for s in states[:5]] == expected_prefix
    assert states[-1].clock == n + 9
    assert states[-1].step == "S"
    old_start = states[0]
    new_start = states[4]
    assert (old_start.quotient, old_start.residue) == (4, 49)
    assert (new_start.quotient, new_start.residue) == (6, 33)
    assert new_start.clock - old_start.clock == 4
    assert new_start.value - old_start.value == 2 * n + 4
    assert capacity(new_start) - capacity(old_start) == -4
    return states, old_start, new_start


def main() -> None:
    print("affine phase-capacity seeded countermodel checks")
    for multiple in (1, 2, 10, 100):
        states, old_start, new_start = lower_fresh_family(multiple)
        print(
            "lowerFresh"
            f" M={multiple} boundary={old_start.clock} current={old_start.value}"
            f" seedSize={18 * multiple + 4} wrap={states[-1].clock}"
            f" old=(q{old_start.quotient},r{old_start.residue},B{capacity(old_start)})"
            f" new=(q{new_start.quotient},r{new_start.residue},B{capacity(new_start)})"
            f" deltaN={new_start.clock-old_start.clock}"
            f" deltaX={new_start.value-old_start.value}"
            f" deltaB={capacity(new_start)-capacity(old_start)}"
        )
    states, old_start, new_start = upper_blocked_family()
    print(
        "upperBlocked"
        f" boundary={old_start.clock} current={old_start.value} seedSize=8"
        f" wrap={states[-1].clock}"
        f" old=(q{old_start.quotient},r{old_start.residue},B{capacity(old_start)})"
        f" new=(q{new_start.quotient},r{new_start.residue},B{capacity(new_start)})"
        f" deltaN={new_start.clock-old_start.clock}"
        f" deltaX={new_start.value-old_start.value}"
        f" deltaB={capacity(new_start)-capacity(old_start)}"
    )
    print("checks=PASS")


if __name__ == "__main__":
    main()
