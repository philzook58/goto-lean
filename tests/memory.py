#!/usr/bin/env python3
"""Check shared-memory translation against native C and kernel-checked Lean proofs."""
import ctypes
import os
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / 'build'
WORK = BUILD / 'memory'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(WORK))


def run(*args):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                            capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise RuntimeError(f'{args}\n{result.stdout}{result.stderr}')
    return result.stdout


run('lake', 'build', 'GotoLean', 'GotoLean.Audit', 'GotoLean.MemoryViews')
run(BUILD / 'bin/goto-cc', '-D__CPROVER__', '-c', 'tests/memory.c', '-o', WORK / 'memory.gb')
# Function, argument count, declaration choices. Do not remove overwritten declarations.
cases = [('cursor_alias', 0, [0, 0, 0]), ('alias_local', 1, [0, 0]),
         ('alias_bytes', 1, [0, 0]), ('alias_member', 1, [0, 0]),
         ('alias_array', 2, [0, 0]), ('one_past', 0, [0, 0]),
         ('backwards', 0, [0, 0]), ('distinct_objects', 0, [0, 0, 0])]
extra = ['stable_uninitialized', 'null_bad', 'bounds_bad', 'dead_bad',
         'store_parameter', 'cursor_parameter', 'escape_local']
names = [name for name, _, _ in cases] + extra
modules = {name: ''.join(word.capitalize() for word in name.split('_')) for name in names}
for name in names:
    path = WORK / f'{modules[name]}.lean'
    run(BUILD / 'bin/goto-lean', WORK / 'memory.gb', '--function', name, '-o', path)
    run('lake', 'env', 'lean', '-o', path.with_suffix('.olean'), path)

run('cc', '-shared', '-fPIC', '-O2', 'tests/memory.c', '-o', WORK / 'native.so')
lib = ctypes.CDLL(str(WORK / 'native.so'))
rng = random.Random(0xA11A5)
runner = [f'import {modules[name]}' for name, _, _ in cases]
expected = []
for name, count, choices in cases:
    fn = getattr(lib, name)
    fn.argtypes, fn.restype = [ctypes.c_uint32] * count, ctypes.c_uint32
    runner += [f'def check_{name} : IO Unit := do']
    rows = [[rng.getrandbits(32) for _ in range(count)] for _ in range(90 if count else 1)]
    for row in rows:
        expected.append(fn(*row))
        args = ' '.join(map(str, row))
        runner += [f'  match (v_{name}.eval {args} 100 {choices}).1 with',
                   '  | .returned (value, _) => IO.println value.toNat',
                   '  | other => throw (IO.userError (reprStr other))']
runner += ['def main : IO Unit := do'] + [f'  check_{name}' for name, _, _ in cases]
(WORK / 'Native.lean').write_text('\n'.join(runner) + '\n')
observed = list(map(int, run('lake', 'env', 'lean', '--run', WORK / 'Native.lean').splitlines()))
assert observed == expected, 'native C and translated Lean disagree'
print(f'PASS {len(expected)} native C/Lean memory comparisons', flush=True)

# The pointer split and pointer-sized loads must follow the input ABI, not the host ABI.
run(BUILD / 'bin/goto-cc', '--32', '-D__CPROVER__', '-c', 'tests/memory.c',
    '-o', WORK / 'memory32.gb')
path = WORK / 'Cursor32.lean'
run(BUILD / 'bin/goto-lean', WORK / 'memory32.gb', '--function', 'cursor_alias', '-o', path)
path.write_text(path.read_text() +
                '\n#guard (v_cursor_alias.eval 10 [0, 0, 0]).1 matches .returned (98, _)\n')
run('lake', 'env', 'lean', path)
print(run('lake', 'env', 'lean', 'tests/Memory.lean').strip(), flush=True)
print('PASS memory lifetimes, checked failures, shared parameter effects and Lean proofs', flush=True)
