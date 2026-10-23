#!/usr/bin/env python3
"""Exercise direct calls, recursion and the checked memory/string library models."""
import ctypes
import os
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / 'build'
WORK = BUILD / 'calls'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(WORK))


def run(*args):
    r = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                       text=True, capture_output=True, timeout=120)
    if r.returncode:
        raise RuntimeError(f'{args}\n{r.stdout}{r.stderr}')
    return r.stdout


run('lake', 'build', 'GotoLean', 'GotoLean.Audit', 'GotoLean.Contracts')
run(BUILD / 'bin/goto-cc', '-D__CPROVER__', '-c', 'tests/calls.c', '-o', WORK / 'calls.gb')
rng = random.Random(0xCA11)
cases = [('nested', [[rng.getrandbits(32)] for _ in range(90)]),
         ('aggregate_call', [[rng.getrandbits(32)] for _ in range(90)]),
         ('factorial', [[n] for n in range(11)]), ('even', [[n] for n in range(21)]),
         ('copy_word', [[x] for x in [0, 1, 256, 65535] +
          [rng.getrandbits(32) for _ in range(90)]]), ('copy_disjoint', [[]])]
names = [name for name, _ in cases] + [
    'callee_bad', 'callee_dead', 'copy_overlap', 'copy_bounds', 'string_bad', 'call_void']
modules = {name: ''.join(s.capitalize() for s in name.split('_')) for name in names}
for name in names:
    path = WORK / f'{modules[name]}.lean'
    run(BUILD / 'bin/goto-lean', WORK / 'calls.gb', '--function', name, '-o', path)
    run('lake', 'env', 'lean', '-o', path.with_suffix('.olean'), path)

run('cc', '-shared', '-fPIC', '-O2', 'tests/calls.c', '-o', WORK / 'native.so')
lib = ctypes.CDLL(str(WORK / 'native.so'))
runner = [f'import {modules[name]}' for name, _ in cases]
runner += ['open GotoLean']
expected = []
for name, rows in cases:
    fn = getattr(lib, name)
    fn.argtypes, fn.restype = [ctypes.c_uint32] * len(rows[0]), ctypes.c_uint32
    runner += [f'def check_{name} : IO Unit := do']
    for row in rows:
        expected.append(fn(*row))
        args = ' '.join(map(str, row))
        runner += [f'  match (v_{name}.eval {args} 500 (List.replicate 128 0)).1 with',
                   '  | .returned (value, _) => IO.println value.toNat',
                   '  | other => throw (IO.userError (reprStr other))']
runner += ['def main : IO Unit := do'] + [f'  check_{name}' for name, _ in cases]
(WORK / 'Native.lean').write_text('\n'.join(runner) + '\n')
observed = list(map(int, run('lake', 'env', 'lean', '--run', WORK / 'Native.lean').splitlines()))
assert observed == expected, 'native C and translated Lean calls disagree'
print(f'PASS {len(expected)} native C/Lean call and library comparisons', flush=True)
run(BUILD / 'bin/goto-cc', '--32', '-D__CPROVER__', '-c', 'tests/calls.c',
    '-o', WORK / 'calls32.gb')
for name, value in [('nested', 26), ('copy_word', 156257)]:
    path = WORK / f'{modules[name]}32.lean'
    run(BUILD / 'bin/goto-lean', WORK / 'calls32.gb', '--function', name, '-o', path)
    arg = 9 if name == 'nested' else 25185
    path.write_text(path.read_text() +
                    f'\n#guard (v_{name}.eval {arg} 100 (List.replicate 20 0)).1 '
                    f'matches .returned ({value}, _)\n')
    run('lake', 'env', 'lean', path)
print(run('lake', 'env', 'lean', 'tests/Calls.lean').strip(), flush=True)
print(run('lake', 'env', 'lean', 'tests/Contracts.lean').strip(), flush=True)
print('PASS recursive execution, callee failures, copy bounds/overlap and string terminators')
