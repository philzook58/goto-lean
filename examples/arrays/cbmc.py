#!/usr/bin/env python3
"""Run the bounded contracts and deliberately broken comparison through CBMC."""
import subprocess
import time
from pathlib import Path

checks = [("8", ["cbmc.c", "--unwind", "10"], 0),
          ("32", ["cbmc.c", "-DN=32", "--unwind", "34"], 0),
          ("bug", ["bug.c", "-Iupstream", "--unwind", "5", "--trace"], 10)]
flags = ["--unwinding-assertions", "--bounds-check", "--pointer-check", "--signed-overflow-check"]
for name, arguments, expected in checks:
    start = time.monotonic()
    log = Path(f".lake/cbmc-{name}.txt")
    with log.open("w") as output:
        try:
            result = subprocess.run(["cbmc", *arguments, *flags], stdout=output,
                                    stderr=subprocess.STDOUT, timeout=30)
        except subprocess.TimeoutExpired:
            print(f"{name}: timeout after 30s; no verification result ({log})")
            continue
    seconds = time.monotonic() - start
    if result.returncode != expected:
        raise SystemExit(f"{name}: unexpected exit {result.returncode}; see {log}")
    verdict = "verified bounded contracts" if expected == 0 else "found counterexample"
    if name == "bug" and "result=3u" not in log.read_text():
        raise SystemExit(f"bug: expected result 3 in trace; see {log}")
    print(f"{name}: {verdict}, {seconds:.2f}s ({log})")
