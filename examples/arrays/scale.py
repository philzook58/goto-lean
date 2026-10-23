#!/usr/bin/env python3
"""Exercise more shapes of C control flow against Lean and independent Python results."""
import itertools
import random
import subprocess
import sys
from collections import Counter

arrays = [list(xs) for n in range(5) for xs in itertools.product([-1, 0, 1], repeat=n)]
rng = random.Random(1)
for n in [8, 16, 32, 64]:
    arrays.extend([sorted(rng.choices(range(-9, 10), k=n)), list(range(n, 0, -1)), [1]*n])
    arrays.extend(rng.choices([-2**31, -1, 0, 1, 2**31-1], k=n) for _ in range(5))
cases, expected = [], []
for xs in arrays:
    n = len(xs)
    prefix = next((i for i in range(1, n) if xs[i-1] > xs[i]), n)
    for key in [-2**31, -1, 0, 1, 2**31-1]:
        cases.append(("fill", n, key, *xs))
        expected.append([0, *([key]*n)])
        cases.append(("find", n, key, *xs))
        expected.append([xs.index(key) if key in xs else n, *xs])
    cases.append(("prefix", n, 0, *xs))
    expected.append([prefix, *xs])
    for pivot in sorted({0, n//2, n}):
        cases.append(("rotate", n, pivot, *xs))
        expected.append([n-pivot, *xs[pivot:], *xs[:pivot]])
    cases.append(("sort", n, 0, *xs))
    expected.append([0, *sorted(xs)])
inputs = "".join(" ".join(map(str, case))+"\n" for case in cases)
expected = [" ".join(map(str, result)) for result in expected]
for command in [[".lake/scale"], ["lake", "env", "lean", "--run", sys.argv[1] if len(sys.argv) > 1 else "Scale.lean"]]:
    result = subprocess.run(command, input=inputs, text=True, capture_output=True, check=True)
    actual = result.stdout.splitlines()
    if actual != expected:
        for i, (got, want) in enumerate(itertools.zip_longest(actual, expected)):
            if got != want:
                raise SystemExit(f"{command}: case {i}: {cases[i]}: {got!r} != {want!r}")
print(f"{len(cases)} native C / Lean / Python agreements: {dict(Counter(c[0] for c in cases))}")
