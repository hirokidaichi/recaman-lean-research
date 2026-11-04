#!/usr/bin/env python3
"""Exercise CI disk provisioning with fake commands; never remove SDKs or swap."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("prepare_ci_swap.sh").resolve()
GIB_KIB = 1024 * 1024
SDKS = ["/usr/local/lib/android", "/usr/share/dotnet", "/opt/ghc",
        "/opt/hostedtoolcache/CodeQL"]
FAKE = r'''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
root = Path(os.environ["CI_SWAP_TEST_ROOT"])
name = Path(sys.argv[0]).name
args = sys.argv[1:]
with (root / "commands.jsonl").open("a") as log:
    log.write(json.dumps([name, *args]) + "\n")
if name == "df":
    if args[0] == "--output=avail":
        key = "AFTER_KIB" if (root / "cleaned").exists() else "BEFORE_KIB"
        print("Avail\n" + os.environ[key])
    else:
        print("simulated disk report")
elif name == "sudo" and args[:3] == ["rm", "-rf", "--"]:
    (root / "cleaned").touch()
'''


class PrepareSwapTests(unittest.TestCase):
    def run_script(self, before, after, **overrides):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fakebin = root / "bin"
            fakebin.mkdir()
            for name in ["df", "sudo", "free"]:
                command = fakebin / name
                command.write_text(FAKE)
                command.chmod(0o755)
            env = dict(os.environ, PATH=f"{fakebin}{os.pathsep}{os.environ['PATH']}",
                       CI_SWAP_TEST_ROOT=tmp, BEFORE_KIB=str(before),
                       AFTER_KIB=str(after), GITHUB_ACTIONS="true", RUNNER_OS="Linux",
                       RUNNER_TEMP=str(root / "runner temp"))
            env.update(overrides)
            result = subprocess.run(["bash", str(SCRIPT)], env=env,
                                    capture_output=True, text=True, timeout=10)
            log = root / "commands.jsonl"
            commands = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
            return result, commands, env["RUNNER_TEMP"]

    def assert_swap(self, commands, runner_temp):
        target = runner_temp + "/recaman-kernel.swap"
        self.assertEqual([c for c in commands if c[:2] == ["sudo", "fallocate"]],
                         [["sudo", "fallocate", "-l", "32G", target]])
        for command in [["sudo", "chmod", "600", target],
                        ["sudo", "mkswap", target], ["sudo", "swapon", target]]:
            self.assertIn(command, commands)

    def test_enough_space_keeps_sdks_and_reserves_full_swap(self):
        result, commands, runner_temp = self.run_script(36 * GIB_KIB, 36 * GIB_KIB)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(any(c[:2] == ["sudo", "rm"] for c in commands))
        self.assert_swap(commands, runner_temp)

    def test_low_space_cleans_only_unused_sdks_before_swap(self):
        result, commands, runner_temp = self.run_script(16 * GIB_KIB, 40 * GIB_KIB)
        self.assertEqual(result.returncode, 0, result.stderr)
        cleanup = ["sudo", "rm", "-rf", "--", *SDKS]
        self.assertIn(cleanup, commands)
        self.assertLess(commands.index(cleanup), next(i for i, c in enumerate(commands)
                                                     if c[:2] == ["sudo", "fallocate"]))
        self.assert_swap(commands, runner_temp)

    def test_still_insufficient_fails_before_allocating_swap(self):
        result, commands, _ = self.run_script(16 * GIB_KIB, 35 * GIB_KIB)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("need 36 GiB", result.stderr)
        self.assertFalse(any(c[:2] == ["sudo", "fallocate"] for c in commands))

    def test_rejects_local_execution_before_running_commands(self):
        result, commands, _ = self.run_script(40 * GIB_KIB, 40 * GIB_KIB,
                                              GITHUB_ACTIONS="")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(commands, [])

    def test_invalid_disk_measurement_fails_without_cleanup(self):
        result, commands, _ = self.run_script("unknown", 40 * GIB_KIB)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(any(c[0] == "sudo" for c in commands))


if __name__ == "__main__":
    unittest.main(verbosity=2)
