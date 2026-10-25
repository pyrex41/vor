#!/usr/bin/env python3
"""Hold the owned process-group identity until its supervisor kills/reaps it."""
import os
import signal
import struct
import subprocess
import sys
import time


def kill_owned_group():
    os.killpg(os.getpgrp(), signal.SIGKILL)


def main():
    if len(sys.argv) < 4:
        return 2
    parent = int(sys.argv[1])
    status_fd = int(sys.argv[2])
    if os.getpid() != os.getpgrp() or parent <= 1 or os.getppid() != parent:
        return 2
    # The worker does not inherit the private status channel. The guardian
    # reports the actual worker's exit and remains the unreaped group leader.
    child = subprocess.Popen(sys.argv[3:], close_fds=True)
    reported = False
    while True:
        if os.getppid() != parent:
            kill_owned_group()
        result = child.poll()
        if result is not None and not reported:
            try:
                os.write(status_fd, struct.pack(">i", result))
                os.close(status_fd)
                os.close(1)
                os.close(2)
            except OSError:
                kill_owned_group()
            reported = True
        # Do not exit after the worker. Holding the leader alive prevents its
        # PGID from being reused before the supervisor's final kill/reap.
        time.sleep(.05)


if __name__ == "__main__":
    sys.exit(main())
