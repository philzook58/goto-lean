#!/usr/bin/env python3
"""Probe the paper's original programs; distinguish translation from verification."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
SOURCE = Path(__file__).resolve().parent
TOOLS = ROOT / 'build/bin'
CBMC = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else TOOLS / 'cbmc'
WORK = ROOT / 'build/paper'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(WORK))


def run(*args, expected=0):
    r = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                       text=True, capture_output=True, timeout=120)
    if r.returncode != expected:
        raise RuntimeError(f'{args}\n{r.stdout}{r.stderr}')
    return r.stdout + r.stderr


run('lake', 'build')
for module, source, entry, defines, checks, verdict in [
    ('Abs', SOURCE / 'abs.c', 'abs', [], ['--signed-overflow-check'], 10),
    ('Binsearch', SOURCE.parent / 'tutorials/memory.c', 'binsearch', [], ['--bounds-check'], 0),
    ('Range', SOURCE / 'assume.c', 'one_to_hundred', [], [], 0),
    ('Before', SOURCE / 'assume.c', 'one_to_hundred', ['-DBEFORE'], [], 10),
    ('After', SOURCE / 'assume.c', 'one_to_hundred', ['-DAFTER'], [], 10),
    ('ArrayAssume', SOURCE / 'array_assume.c', 'main', [], ['--bounds-check'], 10),
]:
    obj, checked = WORK / f'{module}.gb', WORK / f'{module}-checked.gb'
    run(TOOLS / 'goto-cc', *defines, '-c', source, '-o', obj)
    if checks:
        run(TOOLS / 'goto-instrument', *checks, obj, checked)
        obj = checked
    file = WORK / f'Paper{module}.lean'
    run(TOOLS / 'goto-lean', obj, '--function', entry, '-o', file)
    run('lake', 'env', 'lean', '-o', file.with_suffix('.olean'), file)
    log = run(CBMC, obj, '--function', entry, '--no-standard-checks', '--unwind', '6',
              '--unwinding-assertions', '--trace', expected=verdict)
    (WORK / f'{module}.log').write_text(log)
    print(f'{module}: translated; CBMC exit {verdict}', flush=True)

for name, reason in [('lock', 'LOCK'), ('login', 'string_constant'),
                     ('account', 'mutex'), ('loop', 'FUNCTION_CALL f')]:
    obj = WORK / f'{name}.gb'
    run(TOOLS / 'goto-cc', '-c', SOURCE / f'{name}.c', '-o', obj)
    error = run(TOOLS / 'goto-lean', obj, '--function', 'main', '-o', WORK / f'{name}.lean',
                expected=2)
    assert reason in error, error
    (WORK / f'{name}.log').write_text(error)
    print(f'{name}: BLOCKED: {error.strip()}', flush=True)
for file in ['Proofs.lean', 'After.lean']:
    print(run('lake', 'env', 'lean', SOURCE / file).strip(), flush=True)
