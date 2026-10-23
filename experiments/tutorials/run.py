#!/usr/bin/env python3
"""Run from anywhere; optionally pass the path to a matching CBMC binary."""
import os
from pathlib import Path
import shlex
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
source = Path(__file__).resolve().parent
tools = root / 'build/bin'
cbmc = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else tools / 'cbmc'
work = root / 'build/tutorials'
work.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(work))
log = (work / 'run.log').open('w')


def run(command, expected=0):
    command = list(map(str, command))
    print('+', shlex.join(command), flush=True)
    result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
    output = result.stdout + result.stderr
    log.write(shlex.join(command) + '\n' + output + '\n')
    log.flush()
    assert result.returncode == expected, output
    return output


# Generate and compile the Lean modules.
run(['lake', 'build'])
obj, checked = work / 'examples.gb', work / 'checked.gb'
run([tools / 'goto-cc', '-c', source / 'examples.c', '-o', obj])
run([cbmc.parent / 'goto-instrument', '--signed-overflow-check', obj, checked])
names = ['uninitialized', 'guarded', 'abs32', 'abs64', 'before_assume',
         'after_assume', 'range_fixed', 'lock_bug', 'lock_fixed']
for name in names:
    module = ''.join(part.capitalize() for part in name.split('_'))
    file = work / f'{module}.lean'
    binary = checked if name == 'abs32' else obj
    run([tools / 'goto-lean', binary, '--function', name, '-o', file])
    run(['lake', 'env', 'lean', '-o', file.with_suffix('.olean'), file])

# CBMC: six bugs, two safe functions. Check the relevant assertion for each.
for name, prop, expected in [
    ('uninitialized', 'assertion.1', 10), ('guarded', 'assertion.1', 0),
    ('abs32', 'overflow.1', 10), ('abs64', 'assertion.1', 10),
    ('before_assume', 'assertion.1', 10), ('after_assume', 'assertion.1', 10),
    ('range_fixed', 'assertion.1', 0), ('lock_bug', 'assertion.2', 10),
]:
    binary = checked if name == 'abs32' else obj
    run([cbmc, binary, '--function', name, '--no-standard-checks', '--property',
         f'{name}.{prop}', '--trace', '--beautify', '--unwind', '3',
         '--no-unwinding-assertions'], expected)

# Lean checks the discovered models, concrete witnesses, and unbounded invariants.
for file in ['Discover.lean', 'Counterexamples.lean', 'Annotated.lean']:
    output = run(['lake', 'env', 'lean', source / file])
    assert 'sorryAx' not in output and '._native.' not in output, output

# Memory examples: supply CBMC's bounds assertions to both tools.
memory = work / 'memory.gb'
run([tools / 'goto-cc', '-c', source / 'memory.c', '-o', memory])
memory_checked = work / 'memory-checked.gb'
run([cbmc.parent / 'goto-instrument', '--bounds-check', memory, memory_checked])
for name, expected in [('buffer_overflow', 10), ('binsearch', 0)]:
    run([cbmc, memory, '--function', name, '--no-standard-checks', '--bounds-check',
         '--pointer-check', '--unwind', '6', '--unwinding-assertions', '--trace'], expected)
    module = ''.join(part.capitalize() for part in name.split('_'))
    file = work / f'{module}.lean'
    run([tools / 'goto-lean', memory_checked, '--function', name, '-o', file])
    run(['lake', 'env', 'lean', '-o', file.with_suffix('.olean'), file])
output = run(['lake', 'env', 'lean', source / 'Memory.lean'])
assert 'sorryAx' not in output and '._native.' not in output, output

print(f'PASS: tutorial examples and proofs. Output: {work / "run.log"}')
