#!/usr/bin/env python3
"""Run a CI command with periodic Linux resource samples and its exit status."""

from datetime import datetime, timezone
from pathlib import Path
import subprocess
import sys
import time


def snapshot(started: float) -> None:
    print(f"[resources] {datetime.now(timezone.utc).isoformat()} "
          f"elapsed={time.monotonic() - started:.0f}s", flush=True)
    if not sys.platform.startswith("linux"):
        return
    for command in (["free", "-m"],
                    ["ps", "-eo", "pid,ppid,stat,rss,etime,comm", "--sort=-rss"]):
        try:
            result = subprocess.run(command, capture_output=True, text=True,
                                    timeout=10, check=False)
            print("\n".join(result.stdout.splitlines()[:12]), flush=True)
        except (OSError, subprocess.TimeoutExpired) as error:
            print(f"[resources] unavailable: {error}", flush=True)
    for name in ("memory.current", "memory.max", "memory.events"):
        path = Path("/sys/fs/cgroup") / name
        try:
            print(f"[resources] {name}: {path.read_text().strip()}", flush=True)
        except OSError:
            pass


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: ci_with_resources.py COMMAND [ARG ...]", file=sys.stderr)
        return 2
    started = time.monotonic()
    snapshot(started)
    process = subprocess.Popen(sys.argv[1:])
    while True:
        try:
            code = process.wait(timeout=45)
            snapshot(started)
            return code if code >= 0 else 128 - code
        except subprocess.TimeoutExpired:
            snapshot(started)


if __name__ == "__main__":
    sys.exit(main())
