#!/usr/bin/env python3
"""Confirmed research intervals in the daily 06:00–08:00 JST window.

This journal records declared work, not CPU activity. Status never credits an
open interval; recovery records its unconfirmed tail as a gap, not as work.
"""
from __future__ import annotations

import argparse
import copy
import datetime as dt
import fcntl
import json
import os
from pathlib import Path
import sys
import tempfile
import uuid
from zoneinfo import ZoneInfo

JST = ZoneInfo("Asia/Tokyo")
ACTIVE = {"setup", "research", "audit", "handoff"}
PHASES = ACTIVE | {"waiting", "blocked"}
ROOT = Path(__file__).resolve().parent.parent


def bounds(day: str) -> tuple[dt.datetime, dt.datetime]:
    date = dt.date.fromisoformat(day)
    return (dt.datetime.combine(date, dt.time(6), JST),
            dt.datetime.combine(date, dt.time(8), JST))


def instant(value: str) -> dt.datetime:
    stamp = dt.datetime.fromisoformat(value)
    if stamp.tzinfo is None:
        raise ValueError("timestamps must include a timezone")
    return stamp.astimezone(JST)


def blank(day: str) -> dict:
    return dict(version=1, date=day, timezone="Asia/Tokyo", target_seconds=7200,
                events=[], segments=[], unconfirmed_gaps=[], cursor=None)


def union_seconds(intervals: list[tuple[dt.datetime, dt.datetime]]) -> float:
    merged: list[list[dt.datetime]] = []
    for lo, hi in sorted((lo, hi) for lo, hi in intervals if hi > lo):
        if merged and lo <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], hi)
        else:
            merged.append([lo, hi])
    return round(sum((hi-lo).total_seconds() for lo, hi in merged), 3)


def summary(log: dict, now: dt.datetime) -> dict:
    lo, hi = bounds(log["date"])
    work, overtime, other = [], [], {}
    for segment in log["segments"]:
        start, end = instant(segment["start"]), instant(segment["end"])
        if segment["phase"] in ACTIVE:
            work.append((max(start, lo), min(end, hi)))
            overtime.extend([(start, min(end, lo)), (max(start, hi), end)])
        else:
            other.setdefault(segment["phase"], []).append((start, end))
    confirmed = union_seconds(work)
    gaps = [(max(instant(g["start"]), lo), min(instant(g["end"]), hi))
            for g in log["unconfirmed_gaps"]]
    cursor = log["cursor"]
    pending = union_seconds([(max(instant(cursor["at"]), lo), min(now, hi))]) if cursor else 0
    return dict(date=log["date"], now_jst=now.isoformat(),
                confirmed_work_seconds=confirmed, target_seconds=7200,
                shortfall_seconds=round(max(0, 7200-confirmed), 3),
                excluded_non_work_seconds={k: union_seconds(v) for k, v in other.items()},
                unconfirmed_gap_seconds=union_seconds(gaps),
                open_interval_unconfirmed_seconds=pending,
                overtime_work_seconds=union_seconds(overtime), cursor=cursor)


def transition(log: dict, action: str, now: dt.datetime, *, session: str | None = None,
               phase: str | None = None, unit: str | None = None,
               note: str = "") -> tuple[dict, dict]:
    if now.tzinfo is None:
        raise ValueError("use an actual timezone-aware clock")
    now = now.astimezone(JST)
    if log["date"] != now.date().isoformat():
        raise ValueError("past daily journals are read-only")
    if phase is not None and phase not in PHASES:
        raise ValueError("unknown phase")
    state = copy.deepcopy(log)
    cursor = state["cursor"]
    stamp = now.isoformat()
    window_start, deadline = bounds(state["date"])
    if action == "start" and cursor:
        return state, dict(status="already_active", **summary(state, now))
    if action not in {"start", "checkpoint", "stop", "recover"}:
        raise ValueError("unknown journal action")
    if action != "start":
        if not cursor or session != cursor["session"]:
            raise ValueError("the current session token is required; state was not changed")
        if now < instant(cursor["at"]):
            raise ValueError("clock moved backwards; state was not changed")
    if action in {"stop", "recover"} and not note.strip():
        raise ValueError("stop/recover requires a concrete --note")
    if action in {"start", "checkpoint"}:
        next_phase = phase or (cursor["phase"] if cursor else "setup")
        next_unit = unit if unit is not None else (cursor["unit"] if cursor else "")
        if now >= deadline or (next_phase in ACTIVE and now < window_start):
            raise ValueError("active work is allowed only from 06:00 until 08:00 JST")
        if next_phase == "research" and now >= deadline-dt.timedelta(minutes=15):
            raise ValueError("from 07:45 JST use audit/handoff, not a new research interval")
        if next_phase in ACTIVE and not next_unit.strip():
            raise ValueError("an active interval needs a bounded --unit")
    if cursor:
        segment = dict(start=cursor["at"], end=stamp, session=cursor["session"],
                       phase=cursor["phase"], unit=cursor["unit"])
        if action == "recover":
            state["unconfirmed_gaps"].append(dict(**segment, reason=note))
        else:
            state["segments"].append(segment)
    token = str(uuid.uuid4()) if action == "start" else session
    state["cursor"] = (dict(session=token, at=stamp, phase=next_phase, unit=next_unit)
                       if action in {"start", "checkpoint"} else None)
    state["events"].append(dict(at=stamp, action=action, session=token, note=note))
    return state, dict(status=action, **summary(state, now))


def update(path: Path, action: str, now: dt.datetime, **kwargs) -> dict:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.with_suffix(".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        state = json.loads(path.read_text()) if path.exists() else blank(now.astimezone(JST).date().isoformat())
        state, result = transition(state, action, now, **kwargs)
        if result["status"] != "already_active":
            fd, temporary = tempfile.mkstemp(prefix=path.name+".", dir=path.parent)
            try:
                with os.fdopen(fd, "w") as out:
                    json.dump(state, out, ensure_ascii=False, indent=2)
                    out.write("\n")
                    out.flush()
                    os.fsync(out.fileno())
                os.replace(temporary, path)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
        return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("action", choices=["start", "checkpoint", "stop", "recover", "status"])
    ap.add_argument("--session")
    ap.add_argument("--phase", choices=sorted(PHASES))
    ap.add_argument("--unit")
    ap.add_argument("--note", default="")
    ap.add_argument("--date", help="read an earlier journal with status only")
    args = ap.parse_args()
    now = dt.datetime.now(JST)
    day = args.date or now.date().isoformat()
    try:
        bounds(day)
        if args.date and args.action != "status":
            raise ValueError("--date is read-only; there is no command-line clock override")
        path = ROOT / "docs/data/daily_research" / (day+".json")
        if args.action == "status":
            exists = path.exists()
            state = json.loads(path.read_text()) if exists else blank(day)
            result = dict(status="status" if exists else "not_started", journal=str(path),
                          journal_exists=exists, **summary(state, now))
        else:
            result = update(path, args.action, now, session=args.session,
                            phase=args.phase, unit=args.unit, note=args.note)
            result["journal"] = str(path)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (ValueError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
