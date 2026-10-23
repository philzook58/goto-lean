#!/usr/bin/env python3
"""Compare native C, generated Lean, and independent Python array operations."""
import bisect
import itertools
import random
import subprocess
import sys

rng = random.Random(0)
cases = []
for n in range(7):
    for xs in itertools.combinations_with_replacement([-1, 0, 1], n):
        for key in [-2, -1, 0, 1, 2]:
            cases.append((xs, key))
for n in [0, 1, 2, 3, 16, 31, 32, 63, 64, 127, 256]:
    for _ in range(8):
        xs = sorted(rng.choices([-2**31, -100, -1, 0, 1, 100, 2**31-1], k=n))
        for key in [-2**31, -1, 0, 1, 2**31-1]:
            cases.append((xs, key))
inputs = "".join(" ".join(map(str, [len(xs), key, *xs])) + "\n" for xs, key in cases)
expected = [" ".join(map(str, [bisect.bisect_left(xs, key), *reversed(xs)]))
            for xs, key in cases]
for command in [[".lake/replay"], ["lake", "env", "lean", "--run", sys.argv[1] if len(sys.argv) > 1 else "Replay.lean"]]:
    result = subprocess.run(command, input=inputs, text=True, capture_output=True, check=True)
    actual = result.stdout.splitlines()
    if actual != expected:
        for i, (got, want) in enumerate(itertools.zip_longest(actual, expected)):
            if got != want:
                raise SystemExit(f"{command}: case {i}: {cases[i]}: {got!r} != {want!r}")
print(f"{len(cases)} cases: native C = generated Lean = Python; both algorithms checked")
