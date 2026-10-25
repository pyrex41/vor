#!/usr/bin/env python3
"""Owned-process watchdog. No semantic decisions and no payload diagnostics."""
import os
import signal
import subprocess
import sys
import time


def main():
    if len(sys.argv) < 3:
        return 2
    parent = int(sys.argv[1])
    # The supervisor creates this session/group; children cannot inherit an
    # unrelated process group that this guard might subsequently signal.
    if os.getpid() != os.getpgrp() or parent <= 1 or os.getppid() != parent:
        return 2
    child = subprocess.Popen(sys.argv[2:])
    while True:
        if os.getppid() != parent:
            os.killpg(os.getpgrp(), signal.SIGKILL)
            return 2
        result = child.poll()
        if result is not None:
            # Keep the leader until all semantic output is consumed. Exit
            # status remains observable by the owning supervisor.
            return result
        time.sleep(.05)


if __name__ == "__main__":
    sys.exit(main())
