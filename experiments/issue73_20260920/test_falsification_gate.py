#!/usr/bin/env python3

import contextlib
import io
import subprocess
import unittest
from unittest.mock import patch

import falsification_gate as gate


class FalsificationGateTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.real_output = gate.run_baseline(timeout=30)

    def run_gate(self, *args):
        with patch.object(gate, "run_baseline", return_value=self.real_output):
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                return gate.main(list(args))

    def test_real_baseline_is_accepted(self):
        self.assertEqual(self.run_gate(), 0)

    def test_each_known_fault_is_rejected_nonzero(self):
        for fault in gate.FAULTS:
            with self.subTest(fault=fault):
                self.assertNotEqual(self.run_gate("--simulate-fault", fault), 0)

    def test_nonzero_child_is_rejected(self):
        failed = subprocess.CompletedProcess([], 9, stdout="partial", stderr="child failed")
        with patch.object(gate.subprocess, "run", return_value=failed):
            with self.assertRaises(gate.GateFailure):
                gate.run_baseline(timeout=30)

    def test_timeout_is_rejected(self):
        timeout = subprocess.TimeoutExpired(["baseline"], 1)
        with patch.object(gate.subprocess, "run", side_effect=timeout):
            with self.assertRaises(gate.GateFailure):
                gate.run_baseline(timeout=1)


if __name__ == "__main__":
    unittest.main()
