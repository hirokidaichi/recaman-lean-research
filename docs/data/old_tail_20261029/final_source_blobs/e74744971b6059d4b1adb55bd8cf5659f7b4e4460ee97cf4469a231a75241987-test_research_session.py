#!/usr/bin/env python3
"""Time-accounting regressions using simulated clocks and disposable files."""
import copy
import datetime as dt
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import research_session as rs


def clock(h, m=0, s=0):
    return dt.datetime(2026, 10, 23, h, m, s, tzinfo=rs.JST)


class DailyResearchTimeTests(unittest.TestCase):
    def start(self, when=None, phase="research"):
        return rs.transition(rs.blank("2026-10-23"), "start", when or clock(6),
                             phase=phase, unit="C1-depth/first-input")

    def test_two_hour_work_is_measured_and_open_time_is_not_precredited(self):
        state, result = self.start()
        self.assertEqual(result["confirmed_work_seconds"], 0)
        token = result["cursor"]["session"]
        state, result = rs.transition(state, "checkpoint", clock(7, 45),
                                      session=token, phase="audit")
        self.assertEqual(result["confirmed_work_seconds"], 6300)
        state, result = rs.transition(state, "stop", clock(8), session=token,
                                      note="validation and handoff saved at deadline")
        self.assertEqual(result["confirmed_work_seconds"], 7200)
        self.assertEqual(result["shortfall_seconds"], 0)

    def test_early_delivery_waits_without_credit_or_early_research(self):
        with self.assertRaises(ValueError):
            self.start(clock(5, 58, 38))
        state, result = self.start(clock(5, 58, 38), "waiting")
        state, result = rs.transition(state, "checkpoint", clock(6),
                                      session=result["cursor"]["session"], phase="setup")
        self.assertEqual(result["confirmed_work_seconds"], 0)
        self.assertEqual(result["excluded_non_work_seconds"], {"waiting": 82})

    def test_checkpoint_keeps_session_and_assigns_unit_to_correct_interval(self):
        state, result = self.start()
        token = result["cursor"]["session"]
        state, result = rs.transition(state, "checkpoint", clock(6, 30), session=token,
                                      unit="C1-depth/second-input")
        self.assertEqual(result["cursor"]["session"], token)
        self.assertEqual(state["segments"][0]["unit"], "C1-depth/first-input")
        self.assertEqual(result["cursor"]["unit"], "C1-depth/second-input")

    def test_duplicate_start_cannot_create_another_session_or_double_credit(self):
        state, result = self.start()
        before = copy.deepcopy(state)
        state, result = rs.transition(state, "start", clock(6, 30), phase="research", unit="duplicate")
        self.assertEqual(state, before)
        self.assertEqual(result["status"], "already_active")
        self.assertEqual(result["confirmed_work_seconds"], 0)

    def test_crash_recovery_excludes_gap_and_restarts_at_actual_resume(self):
        state, result = self.start()
        token = result["cursor"]["session"]
        state, result = rs.transition(state, "checkpoint", clock(6, 5), session=token)
        state, result = rs.transition(state, "recover", clock(6, 30), session=token,
                                      note="previous turn interrupted after last confirmed checkpoint")
        self.assertEqual(result["confirmed_work_seconds"], 300)
        self.assertEqual(result["unconfirmed_gap_seconds"], 1500)
        self.assertIsNone(result["cursor"])
        state, result = rs.transition(state, "start", clock(6, 30), phase="research", unit="same unfinished unit")
        self.assertNotEqual(result["cursor"]["session"], token)

    def test_wrong_owner_clock_reversal_and_undocumented_early_exit_fail(self):
        state, result = self.start()
        token = result["cursor"]["session"]
        for kwargs, when in [({"session": "stale"}, clock(6, 5)),
                             ({"session": token}, clock(5, 59)),
                             ({"session": token, "note": ""}, clock(6, 5))]:
            with self.subTest(kwargs=kwargs, when=when), self.assertRaises(ValueError):
                rs.transition(state, "stop", when, **kwargs)
        self.assertFalse(state["segments"])

    def test_blocked_time_and_late_saving_are_separate_from_daily_work(self):
        state, result = self.start()
        token = result["cursor"]["session"]
        state, result = rs.transition(state, "checkpoint", clock(6, 10), session=token, phase="blocked")
        state, result = rs.transition(state, "checkpoint", clock(6, 20), session=token, phase="research")
        state, result = rs.transition(state, "stop", clock(8, 0, 5), session=token, note="late close reported")
        self.assertEqual(result["confirmed_work_seconds"], 6600)
        self.assertEqual(result["excluded_non_work_seconds"], {"blocked": 600})
        self.assertEqual(result["overtime_work_seconds"], 5)

    def test_after_deadline_work_is_rejected_and_recovery_does_not_invent_two_hours(self):
        with self.assertRaises(ValueError):
            self.start(clock(8))
        state, result = self.start()
        token = result["cursor"]["session"]
        with self.assertRaises(ValueError):
            rs.transition(state, "checkpoint", clock(8), session=token)
        state, result = rs.transition(state, "recover", clock(8, 1), session=token, note="no further confirmed work")
        self.assertEqual(result["confirmed_work_seconds"], 0)
        self.assertEqual(result["unconfirmed_gap_seconds"], 7200)

    def test_0745_switches_to_audit_instead_of_opening_more_research(self):
        with self.assertRaises(ValueError):
            self.start(clock(7, 45))
        state, result = self.start()
        token = result["cursor"]["session"]
        with self.assertRaises(ValueError):
            rs.transition(state, "checkpoint", clock(7, 45), session=token)
        state, result = rs.transition(state, "checkpoint", clock(7, 45), session=token, phase="audit")
        self.assertEqual(result["cursor"]["phase"], "audit")

    def test_missing_journal_is_not_a_record_of_zero_work_and_cli_has_no_fake_clock(self):
        with tempfile.TemporaryDirectory() as td:
            script = Path(td)/"scripts/research_session.py"
            script.parent.mkdir()
            shutil.copyfile(Path(rs.__file__), script)
            command = [sys.executable, str(script), "status", "--date", "2026-10-23"]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            data = json.loads(result.stdout)
            self.assertEqual(data["status"], "not_started")
            self.assertFalse(data["journal_exists"])
            self.assertFalse((Path(td)/"docs").exists())
            result = subprocess.run(command+["--now", "2026-10-23T06:00:00+09:00"],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)

    def test_atomic_file_survives_rejected_mutation_and_old_days_are_read_only(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td)/"day.json"
            result = rs.update(path, "start", clock(6), phase="research", unit="bounded")
            before = path.read_bytes()
            with self.assertRaises(ValueError):
                rs.update(path, "stop", clock(6, 5), session="wrong", note="invalid owner")
            self.assertEqual(path.read_bytes(), before)
            with self.assertRaises(ValueError):
                rs.transition(json.loads(before), "stop", clock(6)+dt.timedelta(days=1),
                              session=result["cursor"]["session"], note="cannot rewrite yesterday")

    def test_summary_merges_overlapping_intervals_instead_of_double_counting(self):
        state = rs.blank("2026-10-23")
        state["segments"] = [dict(start=clock(6).isoformat(), end=clock(7).isoformat(), phase="research"),
                             dict(start=clock(6, 30).isoformat(), end=clock(7, 30).isoformat(), phase="audit")]
        self.assertEqual(rs.summary(state, clock(8))["confirmed_work_seconds"], 5400)


if __name__ == "__main__":
    unittest.main(verbosity=2)
