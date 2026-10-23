#!/usr/bin/env python3
"""Exercise provenance rejection against a real generated/proved C example."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / 'tools/verification.py'


def run(work, mode, *, succeeds=True):
    result = subprocess.run(['python3', str(RUNNER), mode], cwd=work,
                            text=True, capture_output=True, timeout=120)
    if (result.returncode == 0) != succeeds:
        raise AssertionError(f'{mode}: {result.stdout}{result.stderr}')
    return result


with tempfile.TemporaryDirectory(prefix='verification-', dir=ROOT / 'build') as directory:
    work = Path(directory)
    for name in ['checks.c', 'Proofs.lean', 'lakefile.toml', 'verification.json']:
        shutil.copy2(ROOT / 'examples/checks' / name, work / name)
    source = work / 'checks.c'
    source.write_text('#include "local.h"\n' + source.read_text())
    (work / 'local.h').write_text('#define LOCAL_VALUE 1\n')
    run(work, 'generate')
    assert not (work / '.lake/verification/result.json').exists()
    run(work, 'check')
    run(work, 'status')
    receipt = json.loads((work / '.lake/verification/result.json').read_text())
    assert len(receipt['claims']) == 5
    assert all(e['scope'] == 'unbounded' for e in receipt['generated']['entries'])
    assert 'checked_add | unbounded | 2' in run(work, 'status').stdout

    # Rechecking the old receipt must fail even if a changed file is not used in the theorem.
    for path in [work / 'local.h', source, work / 'Proofs.lean',
                 work / 'Generated/Add.lean', work / '.lake/verification/checked.gb',
                 work / '.lake/verification/Proofs.olean']:
        original = path.read_bytes()
        try:
            path.write_bytes(original + b'\n/* changed */\n')
            run(work, 'status', succeeds=False)
        finally:
            path.write_bytes(original)
    run(work, 'status')

    # A different tool path is a different local toolchain, even with the same version text.
    tool = work / 'alternate-printer'
    shutil.copy2(receipt['generated']['inputs']['tools']['goto-lean']['path'], tool)
    previous = os.environ.get('GOTO_LEAN')
    try:
        os.environ['GOTO_LEAN'] = str(tool)
        run(work, 'status', succeeds=False)
    finally:
        if previous is None:
            os.environ.pop('GOTO_LEAN', None)
        else:
            os.environ['GOTO_LEAN'] = previous
    run(work, 'status')

    config = work / 'verification.json'
    original = config.read_bytes()
    for change in ['macro', 'entry', 'ABI']:
        policy = json.loads(original)
        if change == 'macro':
            policy['compile'].append('-DNEW_CONFIGURATION=1')
        elif change == 'ABI':
            policy['compile'].append('--32')
        else:
            policy['entries'][0]['function'] = 'checked_add'
        config.write_text(json.dumps(policy))
        run(work, 'status', succeeds=False)
        config.write_bytes(original)
    run(work, 'status')

    # A missing source assertion must fail the independent expected inventory.
    saved_source = source.read_text()
    source.write_text(saved_source.replace(
        '__CPROVER_assert(result > x, "increment increases the value");', ';'))
    rejected = run(work, 'generate', succeeds=False)
    assert 'property inventory' in rejected.stderr
    assert not (work / '.lake/verification/result.json').exists()
    source.write_text(saved_source)

    # Turning a safety flag off must not just produce a weaker green receipt.
    policy = json.loads(original)
    policy['checks'].remove('--signed-overflow-check')
    config.write_text(json.dumps(policy))
    rejected = run(work, 'generate', succeeds=False)
    assert 'property inventory' in rejected.stderr
    config.write_bytes(original)

    # Named claims are actually resolved and audited after a fresh proof build.
    policy = json.loads(original)
    policy['entries'][0]['claim'] = 'CheckExamples.missing'
    config.write_text(json.dumps(policy))
    run(work, 'generate')
    rejected = run(work, 'check', succeeds=False)
    assert 'CheckExamples.missing' in rejected.stderr
    assert not (work / '.lake/verification/result.json').exists()
    # An existing, axiom-free theorem of the wrong statement must also be rejected.
    policy = json.loads(original)
    policy['entries'][0]['claim'] = 'CheckExamples.addition'
    config.write_text(json.dumps(policy))
    run(work, 'generate')
    rejected = run(work, 'check', succeeds=False)
    assert 'Type mismatch' in rejected.stderr
    assert not (work / '.lake/verification/result.json').exists()
    config.write_bytes(original)
    run(work, 'generate')
    run(work, 'check')
    run(work, 'status')

print('PASS receipts: positive checks; stale headers/source/config/Lean/GOTO/proof rejected;')
print('missing assertions, disabled instrumentation, unknown and wrong-statement claims rejected')
