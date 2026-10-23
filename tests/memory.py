#!/usr/bin/env python3
"""Check shared-memory translation against native C and kernel-checked Lean proofs."""
import ctypes
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / 'build'
WORK = BUILD / 'memory'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(WORK), LEAN_NUM_THREADS='1')


def run(*args, code=0):
    if args[:3] == ('lake', 'env', 'lean'):
        args = (*args[:3], '-j1', '-M1024', *args[3:])
    result = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                            capture_output=True, text=True, timeout=120)
    if result.returncode != code:
        raise RuntimeError(f'{args}\n{result.stdout}{result.stderr}')
    return result.stdout


run('lake', 'build', 'GotoLean', 'GotoLean.Audit', 'GotoLean.MemoryViews', 'GotoLean.Termination')
run(BUILD / 'bin/goto-cc', '-D__CPROVER__', '-c', 'tests/memory.c', '-o', WORK / 'memory.gb')
# Function, argument count, declaration choices. Do not remove overwritten declarations.
cases = [('cursor_alias', 0, [0, 0, 0]), ('alias_local', 1, [0, 0]),
         ('alias_bytes', 1, [0, 0]), ('alias_member', 1, [0, 0]),
         ('alias_array', 2, [0, 0]), ('one_past', 0, [0, 0]),
         ('backwards', 0, [0, 0]), ('distinct_objects', 0, [0, 0, 0]),
         ('offset_good', 1, [0, 0]), ('separate_good', 1, [0, 0, 0]),
         ('heap_roundtrip', 1, [0, 0, 1, 0, 0]), ('heap_null', 0, []), ('heap_release', 1, [0, 0, 1, 0])]
extra = ['stable_uninitialized', 'null_bad', 'bounds_bad', 'dead_bad',
         'store_parameter', 'cursor_parameter', 'escape_local', 'offset_bad', 'separate_bad', 'heap_dead', 'heap_double_free',
         'heap_interior', 'heap_bounds', 'heap_stack', 'heap_unchecked']
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
path = WORK / 'Heap32.lean'
run(BUILD / 'bin/goto-lean', WORK / 'memory32.gb', '--function', 'heap_release', '-o', path)
path.write_text(path.read_text() +
    '\n#guard (v_heap_release.eval 41 20 [0, 0, 1, 0]).1 matches .returned (41, _)\n'
    '#guard (v_heap_release.eval 41 20 [0, 0, 0]).1 matches .returned (41, _)\n')
run('lake', 'env', 'lean', path)
print(run('lake', 'env', 'lean', 'tests/Memory.lean').strip(), flush=True)
print(run('lake', 'env', 'lean', 'tests/Heap.lean').strip(), flush=True)
run(BUILD / 'bin/goto-instrument', '--pointer-check', '--bounds-check',
    WORK / 'memory.gb', WORK / 'heap-checked.gb')
path = WORK / 'HeapChecked.lean'
run(BUILD / 'bin/goto-lean', WORK / 'heap-checked.gb', '--function', 'heap_roundtrip', '-o', path)
path.write_text(path.read_text() +
    '\n#guard (v_heap_roundtrip.eval 41 20 [0, 0, 1, 0, 0]).1 matches .returned (41, _)\n')
run('lake', 'env', 'lean', path)
print('PASS memory lifetimes, checked failures, shared parameter effects and Lean proofs', flush=True)

if cbmc := shutil.which(os.environ.get('CBMC', 'cbmc')):
    # Match the Lean model's explicit allocation-failure branch.
    for name, property_suffix in [
            ('heap_roundtrip', ''), ('heap_release', ''), ('heap_null', ''),
            ('heap_dead', 'pointer_dereference.9'),
            ('heap_double_free', 'precondition_instance.10'),
            ('heap_interior', 'precondition_instance.3'),
            ('heap_bounds', 'pointer_dereference.5'),
            ('heap_stack', 'precondition_instance.2'),
            ('heap_unchecked', 'pointer_dereference.1')]:
        output = run(cbmc, WORK / 'memory.gb', '--function', name, '--pointer-check',
                     '--bounds-check', '--malloc-may-fail', '--json-ui',
                     code=10 if property_suffix else 0)
        (WORK / (name + '-cbmc.json')).write_text(output)
        failures = [r['property'] for m in json.loads(output) for r in m.get('result', [])
                    if r['status'] == 'FAILURE']
        # An unrelated failure must not make a negative control pass.
        if property_suffix:
            assert name + '.' + property_suffix in failures, (name, failures)
        else:
            assert not failures, (name, failures)
    print('PASS CBMC heap controls, including allocation failure', flush=True)

# Link the real CBMC library. A compile-only .gb has no entry/reachable library bodies.
run(BUILD / 'bin/goto-cc', 'tests/heap-library.c', '-o', WORK / 'heap-library-raw.gb')
run(BUILD / 'bin/goto-instrument', '--add-library', '--malloc-may-fail',
    '--pointer-check', '--bounds-check', WORK / 'heap-library-raw.gb', WORK / 'heap-library.gb')
library_cases = ['library_roundtrip', 'library_calloc', 'library_calloc_overflow',
                 'library_double_free', 'library_dead', 'primitive_zero',
                 'primitive_stable', 'primitive_bad', 'primitive_null']
for name in library_cases:
    path = WORK / (''.join(word.capitalize() for word in name.split('_')) + '.lean')
    run(BUILD / 'bin/goto-lean', WORK / 'heap-library.gb', '--function', name, '-o', path)
    run('lake', 'env', 'lean', '-o', path.with_suffix('.olean'), path)
print(run('lake', 'env', 'lean', 'tests/HeapLibrary.lean').strip(), flush=True)

# Changing CBMC's failure policy must change the translated library behavior too.
for flags, outcome in [(['--no-malloc-may-fail'], '.returned (41, _)'),
                       (['--malloc-may-fail', '--malloc-fail-assert'], '.assertionFailed _')]:
    run(BUILD / 'bin/goto-instrument', '--add-library', *flags,
        WORK / 'heap-library-raw.gb', WORK / 'heap-mode.gb')
    path = WORK / 'HeapMode.lean'
    run(BUILD / 'bin/goto-lean', WORK / 'heap-mode.gb',
        '--function', 'library_roundtrip', '-o', path)
    path.write_text(path.read_text() +
        '\n#guard (v_library_roundtrip.eval 41 100 (List.replicate 100 0)).1 '
        'matches .returned (41, _)\n' +
        '#guard (v_library_roundtrip.eval 41 100 ((List.replicate 100 0).set 4 1)).1 '
        f'matches {outcome}\n')
    run('lake', 'env', 'lean', path)
print('PASS loaded-library proofs and malloc failure policies', flush=True)
if cbmc := shutil.which(os.environ.get('CBMC', 'cbmc')):
    expected_failure = {
        'library_double_free': 'free argument must be NULL or valid pointer',
        'library_dead': 'dereference failure: deallocated dynamic object in *p',
        'primitive_bad': 'arbitrary bytes need not be zero',
    }
    for name in library_cases:
        output = run(cbmc, WORK / 'heap-library.gb', '--function', name,
                     '--no-standard-checks', '--json-ui', code=10 if name in expected_failure else 0)
        (WORK / (name + '-cbmc.json')).write_text(output)
        failures = [r for m in json.loads(output) for r in m.get('result', [])
                    if r['status'] == 'FAILURE']
        if name in expected_failure:
            assert any(r['description'] == expected_failure[name] for r in failures), (name, failures)
        else:
            assert not failures, (name, failures)
    print('PASS CBMC loaded-library and allocation-primitive controls', flush=True)
