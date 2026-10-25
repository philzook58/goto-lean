#!/usr/bin/env python3
"""Paired option/global controls: check the named CBMC failure and certify its Lean replay."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT / 'build'
WORK = BUILD / 'options'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_NUM_THREADS='1')


def run(*args, code=0):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                            capture_output=True, text=True, timeout=120)
    if result.returncode != code:
        raise RuntimeError(f'{args}\n{result.stdout}{result.stderr}')
    return result.stdout


def certify(binary, name, property_id=None, *, bits=8, choices='List.replicate 100 0', rejected=False):
    path = WORK / f'{name}.lean'
    run(BUILD / 'bin/goto-lean', binary, '--function', name, '--object-bits', bits, '-o', path)
    text = path.read_text().replace('import GotoLean\n', 'import GotoLean\nimport GotoLean.Audit\n')
    frame = f'v_{name}.initial'
    step = f'v_{name}.step'
    describe = '(fun f ↦ reprStr f.1)'
    evaluated = f'(GotoLean.evalLoop {step} {describe} 100 {frame} ({choices})).1'
    if property_id:
        sites = [json.loads(m[0]) for m in re.finditer(r'"(?:[^"\\]|\\.)*"', text)]
        site = next(s for s in sites if f'; property {property_id};' in s)
        outcome = f'.assertionFailed {json.dumps(site)}'
        text += f'''
open GotoLean
/-- A reachable violation of {property_id}, including a refutation of safety. -/
theorem certificate :
    Executes {step} {frame} ({outcome}) ∧ ¬ (run {step} {frame}).wp (fun _ ↦ True) := by
  have h : {evaluated} = {outcome} := by decide +kernel
  have execution := evalLoop_exec {step} {describe} 100 {frame} ({choices})
  have failure := failure_refutes {step} {describe} {frame} 100 ({choices})
    (by simp only [h, Outcome.isAssertionFailure]) (fun _ ↦ True)
  exact ⟨by simpa only [h, Outcome.Corresponds] using execution, failure.2⟩
'''
    else:
        constructor = 'assumptionRejected' if rejected else 'returned'
        text += f'''
open GotoLean
/-- A concrete execution reaching {constructor} with all reached checks satisfied. -/
theorem certificate : ∃ value, Executes {step} {frame} (.{constructor} value) := by
  have h : (match {evaluated} with | .{constructor} _ => true | _ => false) = true := by
    decide +kernel
  have execution := evalLoop_exec {step} {describe} 100 {frame} ({choices})
  cases result : {evaluated} <;> simp only [result] at h
  all_goals try contradiction
  exact ⟨_, by simpa only [result, Outcome.Corresponds] using execution⟩
'''
    path.write_text(text + '\n#check_axioms certificate\n')
    output = run('lake', 'env', 'lean', '-j1', '-M1024', path)
    assert 'sorryAx' not in output and 'Lean.ofReduceBool' not in output, output
    if cbmc:
        entry = [] if name == '__CPROVER__start' else ['--function', name]
        output = run(cbmc, binary, *entry, '--object-bits', bits,
                     '--no-standard-checks', '--json-ui', code=10 if property_id else 0)
        (WORK / f'{name}-cbmc.json').write_text(output)
        failures = [r['property'] for m in json.loads(output) for r in m.get('result', [])
                    if r['status'] == 'FAILURE']
        assert property_id in failures if property_id else not failures, failures
    print(f'PASS {name}: {property_id or constructor} (object bits={bits})', flush=True)


cbmc = shutil.which(os.environ.get('CBMC', 'cbmc'))
run('lake', 'build', 'GotoLean', 'GotoLean.Audit')
raw, checked = WORK / 'raw.gb', WORK / 'checked.gb'
run(BUILD / 'bin/goto-cc', '-c', 'tests/options.c', '-o', raw)
run(BUILD / 'bin/goto-instrument', '--unsigned-overflow-check', '--conversion-check',
    '--enum-range-check', '--pointer-overflow-check', '--bounds-check', '--pointer-check', raw, checked)
for stem, property_class in [('unsigned', 'overflow.1'), ('conversion', 'overflow.1'),
                             ('enum', 'enum-range-check.1'), ('pointer', 'pointer_arithmetic.2'),
                             ('globals', 'assertion.1')]:
    certify(checked, stem + '_good')
    certify(checked, stem + '_bad', stem + '_bad.' + property_class)
certify(checked, 'table_bad', 'table_bad.array_bounds.1')

# The exit model ends in assume(false); its positive certificate is explicitly a rejected path.
# Force malloc's leak-monitor choice, rather than letting an untracked leak escape the replay.
cleanup = WORK / 'cleanup.gb'
run(BUILD / 'bin/goto-cc', '--function', 'cleanup_good', 'tests/options.c', '-o', raw)
run(BUILD / 'bin/goto-instrument', '--add-library', '--malloc-may-fail',
    '--memory-cleanup-check', raw, cleanup)
certify(cleanup, 'cleanup_good', choices='(List.replicate 100 0).set 13 1', rejected=True)
certify(cleanup, 'cleanup_bad', 'exit.memory-leak.1', choices='(List.replicate 100 0).set 13 1')
certify(cleanup, '__CPROVER__start', bits=12, rejected=True)

for abi in [32, 64]:
    run(BUILD / 'bin/goto-cc', f'--{abi}', '-c', 'tests/options.c', '-o', raw)
    for bits in [3, 12, abi - 4]:
        certify(raw, 'object_capacity', bits=bits)
    certify(raw, 'malloc_limit', bits=abi - 4)
    path = WORK / 'limit.lean'
    for invalid in ['0', str(abi), '-1', '4junk', '999999999999999999999']:
        path.write_text('preserve output\n')
        run(BUILD / 'bin/goto-lean', raw, '--function', 'object_capacity',
            '--object-bits', invalid, '-o', path, code=2)
        assert path.read_text() == 'preserve output\n'
    run(BUILD / 'bin/goto-lean', raw, '--function', 'object_capacity', '--object-bits', 2, '-o', path)
    sites = [json.loads(m[1]) for m in re.finditer(r'Memory.alloc ("(?:[^"\\]|\\.)*")', path.read_text())]
    site = json.dumps(sites[2] + '; memory allocation')
    path.write_text(path.read_text() +
                    '\n#guard (v_object_capacity.eval 100 (List.replicate 100 0)).1 '
                    f'== .assertionFailed {site}\n')
    run('lake', 'env', 'lean', '-j1', '-M1024', path)
print('PASS 32/64-bit pointer splits, allocation limits, ID exhaustion and invalid options', flush=True)
