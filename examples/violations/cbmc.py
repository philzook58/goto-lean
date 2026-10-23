#!/usr/bin/env python3
"""Expect the named property to fail in each bug, and all checks to pass in its repair."""
import os
from pathlib import Path
import subprocess

cases = [
    ('maximum', 'assertion.1'),
    ('add', 'overflow.1'),
    ('negate', 'overflow.1'),
    ('divide_zero', 'division-by-zero.1'),
    ('divide_overflow', 'overflow.1'),
    ('shift', 'undefined-shift.1'),
    ('index', 'array_bounds.1'),
    ('null', 'pointer_dereference.1'),
    ('one_past', 'pointer_dereference.2'),
    ('lifetime', 'pointer_dereference.1'),
    ('uninitialized', 'assertion.1'),
    ('loop_bound', 'array_bounds.1'),
]
for name, kind in cases:
    property_id = f'bug_{name}.{kind}'
    for prefix in ['bug', 'fixed']:
        function = f'{prefix}_{name}'
        command = [os.environ.get('CBMC', 'cbmc'), '.lake/verification/checked.gb',
                   '--function', function, '--no-standard-checks',
                   '--unwind', '6', '--unwinding-assertions', '--trace']
        if prefix == 'bug':
            command += ['--property', property_id]
        result = subprocess.run(command, text=True, capture_output=True, timeout=60)
        log = result.stdout + result.stderr
        path = Path('.lake') / f'{function}.log'
        path.write_text(log)
        if prefix == 'bug':
            expected = result.returncode == 10 and any(
                line.startswith(f'[{property_id}]') and line.endswith(': FAILURE')
                for line in log.splitlines())
        else:
            expected = result.returncode == 0 and 'VERIFICATION SUCCESSFUL' in log
        if not expected:
            raise SystemExit(f'{function}: unexpected result; see {path}')
    print(f'{name}: named violation found; repair passes all checks', flush=True)
