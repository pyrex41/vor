"""Keep an unreaped process-group leader until the owner kills the whole group."""
import json
from pathlib import Path
import subprocess
import sys


def main():
    target = Path(sys.argv[1])
    try:
        code = subprocess.run(sys.argv[2:], check=False).returncode
    except OSError:
        code = 127
    # Publish atomically so the owner cannot read a partially written status.
    temporary = target.with_suffix(".tmp")
    with temporary.open("x") as output:
        json.dump({"exit_code": code}, output)
    temporary.rename(target)
    sys.stdin.buffer.read(1)


if __name__ == "__main__":
    main()
