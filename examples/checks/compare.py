#!/usr/bin/env python3
"""Run the certified input table against compiled C and compare 32-bit results."""
import ctypes
import os
from pathlib import Path
import subprocess

subprocess.run([os.environ.get('CC', 'cc'), '-std=c11', '-shared', '-fPIC',
                '-Wall', '-Wextra', '-Werror', '-include', 'assert.h',
                '-D__CPROVER_assume(p)=assert(p)', '-D__CPROVER_assert(p,msg)=assert(p)',
                'checks.c', '-o', '.lake/cases.so'], check=True)
native = ctypes.CDLL(str(Path('.lake/cases.so').resolve()))
output = subprocess.run(['lake', 'env', 'lean', '-j1', '-M1024', '--run', 'Cases.lean'],
                        text=True, capture_output=True, timeout=120)
if output.returncode:
    raise SystemExit(output.stdout + output.stderr)
counts = {}
for line in output.stdout.splitlines():
    if not line.startswith('checked_'):
        continue  # The file also prints its axiom audit.
    function, name, x, y, expected = line.split()
    f = getattr(native, function)
    f.restype = ctypes.c_uint32  # Compare bit patterns, including signed C returns.
    args = [int(x), int(y)] if function in ['checked_divide', 'checked_shift'] else [int(x)]
    f.argtypes = [ctypes.c_uint32 if function in ['checked_shift', 'checked_index']
                 else ctypes.c_int32] * len(args)
    actual = f(*args)
    assert actual == int(expected), (function, name, args, actual, expected)
    counts[function] = counts.get(function, 0) + 1
assert counts == {'checked_add': 20, 'checked_abs': 20, 'checked_index': 4,
                  'checked_divide': 20, 'checked_shift': 20}, counts
print('84 certified admitted inputs: native C = Lean; C assumptions/assertions enabled')
