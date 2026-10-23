#!/usr/bin/env python3
"""Measure fresh Lean proof checks and separately bounded CBMC contracts."""
import json
from pathlib import Path
import subprocess
import time

results = []
for name in ['Fill', 'Find', 'IsSortedUntil', 'Rotate', 'BubbleSort']:
    start = time.monotonic()
    subprocess.run(['lake', 'env', 'lean', f'Proofs/{name}.lean'], check=True)
    seconds = round(time.monotonic()-start, 3)
    results.append(dict(tool='Lean', example=name, seconds=seconds, status='checked'))
    print(f'Lean {name}: {seconds:.3f}s (all lengths, imports already built)', flush=True)
for bound in [4, 8, 16]:
    for case, name in enumerate(['fill', 'find', 'prefix', 'rotate', 'sort'], 1):
        command = ['cbmc', 'scale_cbmc.c', f'-DCASE={case}', f'-DN={bound}',
                   '--unwind', str(bound+3), '--unwinding-assertions', '--bounds-check',
                   '--pointer-check', '--signed-overflow-check', '--div-by-zero-check']
        start = time.monotonic()
        log = Path(f'.lake/scale-cbmc-{name}-{bound}.txt')
        with log.open('w') as output:
            try:
                run = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, timeout=10)
                if run.returncode != 0:
                    raise SystemExit(f'{name}/{bound}: unexpected CBMC exit {run.returncode}; see {log}')
                status = 'verified'
            except subprocess.TimeoutExpired:
                status = 'timeout (inconclusive)'
        seconds = round(time.monotonic()-start, 3)
        results.append(dict(tool='CBMC', example=name, bound=bound, seconds=seconds, status=status))
        print(f'CBMC {name}/{bound}: {status}, {seconds:.3f}s', flush=True)
Path('.lake/scaling-results.json').write_text(json.dumps(results, indent=2)+'\n')
