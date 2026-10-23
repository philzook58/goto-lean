#!/usr/bin/env python3
"""Check the pinned source snapshot and create the one-comparison mutation."""
import hashlib
import json
from pathlib import Path

metadata = json.loads(Path("upstream/SOURCE.json").read_text())
for name, expected in metadata["sha256"].items():
    actual = hashlib.sha256((Path("upstream") / name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"upstream/{name}: source hash mismatch")

# The handwritten entry shares rotation's callee; this generated file only imports it.
Path('Generated/Reverse.lean').write_text('import Entries.Reverse\n')

source = Path('upstream/lower_bound.c').read_text()
assert source.count('a[middle] < v') == 1
Path('.lake/lower_bound_bug.c').write_text(
    source.replace('a[middle] < v', 'a[middle] <= v')
          .replace('size_type lower_bound(', 'size_type lower_bound_bug('))
