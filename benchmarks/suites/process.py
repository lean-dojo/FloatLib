"""Run one child process with measured time and a soft RSS ceiling inside the outer cgroup."""
from __future__ import annotations
import os
import signal
import subprocess
import time
from pathlib import Path


def run(command, *, cwd, log, timeout, env=None, stdin=None, stdout=None,
        rss_kib=8 * 1024 * 1024):
    """The returned peak is sampled every 50ms, not an exact kernel high-water mark."""
    peak, termination = 0, ""
    start = time.monotonic()
    utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with Path(log).open("w") as stream:
        process = subprocess.Popen(command, cwd=cwd, env=env or os.environ,
                                   stdout=stdout if stdout is not None else stream,
                                   stderr=stream, stdin=stdin, start_new_session=True)
        while process.poll() is None:
            try:
                text = Path(f"/proc/{process.pid}/status").read_text()
                rss = next((int(line.split()[1]) for line in text.splitlines()
                            if line.startswith("VmRSS:")), 0)
                peak = max(peak, rss)
            except (FileNotFoundError, ProcessLookupError):
                pass
            if peak > rss_kib:
                termination = "memory_limit"
            elif time.monotonic() - start > timeout:
                termination = "timeout"
            if termination:
                os.killpg(process.pid, signal.SIGKILL)
                break
            time.sleep(0.05)
        code = process.wait()
    return {"exit_code": code, "termination": termination, "measurement_utc": utc,
            "elapsed_seconds": time.monotonic() - start,
            "sampled_peak_rss_kib": peak, "sample_period_seconds": 0.05}
