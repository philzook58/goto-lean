#!/usr/bin/env python3
"""Check named positive/negative controls; every successful bounded proof checks unwinding."""
import json
import os
import resource
import subprocess
from check import HERE, WORK


def memory_limit():
    resource.setrlimit(resource.RLIMIT_AS, (1536 * 1024**2,) * 2)


cases = [('slide', 'slide_small', None), ('slide', 'slide_no_double_merge', None),
         ('lookup', 'lookup_case', None),
         ('mutant', 'slide_small', None),  # Mass conservation alone misses double merging.
         ('mutant', 'slide_no_double_merge', 'slide_no_double_merge.assertion.1'),
         ('slide', 'slide_large', 'slideArray.undefined-shift.2'),
         ('json', 'json_validation_claim', 'json_validation_claim.assertion.1'),
         ('lookup', 'lookup_deleted_claim', 'lookup_deleted_claim.assertion.1')]
for source, entry, violation in cases:
    result = subprocess.run([os.environ.get('CBMC', 'cbmc'), str(WORK / f'{source}-checked.gb'),
                             '--function', entry, '--no-standard-checks', '--unwind', '10',
                             '--unwinding-assertions', '--json-ui'], cwd=HERE, capture_output=True,
                            text=True, timeout=45, preexec_fn=memory_limit)
    (WORK / f'{source}-{entry}-cbmc.json').write_text(result.stdout + result.stderr)
    assert result.returncode == (10 if violation else 0), result.stdout[-2000:] + result.stderr
    properties = [p for item in json.loads(result.stdout) for p in item.get('result', [])]
    assert properties
    assert all(p['status'] in ('SUCCESS', 'FAILURE', 'UNKNOWN') for p in properties)
    failures = [p['property'] for p in properties if p['status'] == 'FAILURE']
    assert failures == [violation] if violation else not failures, failures
    if not violation:
        assert all(p['status'] == 'SUCCESS' for p in properties), 'incomplete positive check'
    print(f'{source}/{entry}: {violation or "all checks and unwinding pass"}', flush=True)
print('Eight named controls checked. The full symbolic JSON domain remains unproved.')
