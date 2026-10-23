#!/usr/bin/env python3
"""Check every inserted safety check and C assertion for symbolic arrays of size <= 4."""
from pathlib import Path
import subprocess

build = Path('.lake/safety')
build.mkdir(parents=True, exist_ok=True)
checks = ['--pointer-check', '--bounds-check', '--signed-overflow-check',
          '--div-by-zero-check', '--undefined-shift-check']
for case, name in enumerate(['fill', 'find', 'prefix', 'rotate', 'sort',
                             'lower_bound', 'reverse'], 1):
    raw, checked = build / f'{name}-raw.gb', build / f'{name}.gb'
    subprocess.run(['../../build/bin/goto-cc', '-std=c11', '-DN=4', f'-DCASE={case}',
                    '-c', 'scale_cbmc.c', '-o', raw], check=True)
    subprocess.run(['../../build/bin/goto-instrument', *checks, raw, checked],
                   check=True, stdout=subprocess.DEVNULL)
    command = ['cbmc', str(checked), '--function', 'main', '--no-standard-checks', '--unwind', '6',
               '--unwinding-assertions']
    result = subprocess.run(command, text=True, capture_output=True, timeout=120)
    (build / f'{name}.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise SystemExit(f'{name}: failed; see {build / (name + ".log")}')
    print(f'{name}: checks passed (all inputs, N=4; unwinding checked)', flush=True)
