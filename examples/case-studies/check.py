#!/usr/bin/env python3
"""Regenerate three small case studies and compare complete results with native C."""
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORK = HERE / '.lake/check'
ENV = dict(os.environ, LEAN_NUM_THREADS='1')
TOOLS = {name: os.environ.get(env, str(ROOT / 'build/bin' / name)) for name, env in
         [('goto-cc', 'GOTO_CC'), ('goto-instrument', 'GOTO_INSTRUMENT'), ('goto-lean', 'GOTO_LEAN')]}
CHECKS = ['--bounds-check', '--signed-overflow-check', '--div-by-zero-check',
          '--undefined-shift-check', '--pointer-check']


def run(*command, code=0, **kwargs):
    result = subprocess.run(list(map(str, command)), cwd=HERE, env=ENV,
                            capture_output=True, text=True, timeout=180, **kwargs)
    if result.returncode != code:
        raise RuntimeError(f'{command}\n{result.stdout[-5000:]}{result.stderr[-5000:]}')
    return result.stdout


def packed(xs):
    return sum(x << (8*i) for i, x in enumerate(xs))


def slide_expected(value):
    tiles = [x for i in range(4) if (x := (value >> (8*i)) & 255)]
    result, score, i = [], 0, 0
    while i < len(tiles):
        if i + 1 < len(tiles) and tiles[i] == tiles[i+1]:
            result.append(tiles[i] + 1)
            score += 1 << result[-1]
            i += 2
        else:
            result.append(tiles[i])
            i += 1
    return (score << 32) | packed(result)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((HERE / 'upstream/SOURCE.json').read_text())
    for name, info in manifest['files'].items():
        assert hashlib.sha256((HERE / 'upstream' / name).read_bytes()).hexdigest() == info['sha256'], name
    (HERE / 'Generated').mkdir(exist_ok=True)
    for name, entry in [('json', 'json_case'), ('slide', 'slide_case'), ('lookup', 'lookup_case')]:
        raw, checked = WORK / f'{name}.gb', WORK / f'{name}-checked.gb'
        run(TOOLS['goto-cc'], '-D__CPROVER__', '-std=c11', '-c', HERE / f'{name}.c', '-o', raw)
        run(TOOLS['goto-instrument'], *CHECKS, raw, checked)
        run(TOOLS['goto-lean'], checked, '--function', entry, '-o', HERE / 'Generated' / f'{name.capitalize()}.lean')
    run(TOOLS['goto-lean'], WORK / 'json-checked.gb', '--function', 'jsmn_init',
        '-o', HERE / 'Generated/Init.lean')
    # One deliberate implementation mutation; the vendored source stays untouched.
    original = (HERE / 'upstream/2048/2048.c').read_text()
    assert original.count('stop = t+1;') == 1
    mutant = WORK / '2048-stop-removed.c'
    mutant.write_text(original.replace('stop = t+1;', '/* deliberate double-merge mutation */'))
    wrapper = WORK / 'slide-mutant.c'
    wrapper.write_text((HERE / 'slide.c').read_text().replace('"upstream/2048/2048.c"',
                                                            json.dumps(str(mutant))))
    run(TOOLS['goto-cc'], '-D__CPROVER__', '-std=c11', '-I', HERE, '-c', wrapper,
        '-o', WORK / 'mutant.gb')
    run(TOOLS['goto-instrument'], *CHECKS, WORK / 'mutant.gb',
        WORK / 'mutant-checked.gb')
    # Keep the existing kernel replay profile: full pointer-check replay still exceeds 1 GiB.
    # Native/Lean comparisons and CBMC controls use json-checked.gb with every CHECKS flag.
    run(TOOLS['goto-instrument'], *[flag for flag in CHECKS if flag != '--pointer-check'],
        WORK / 'json.gb', WORK / 'json-replay-checked.gb')
    sites = 'import GotoLean\nnamespace ViolationSites\n'
    violations = [('JsonClaim', 'json-replay', 'json_validation_claim', 'json_validation_claim.assertion.1'),
                  ('BigSlide', 'slide', 'slide_large', 'slideArray.undefined-shift.2'),
                  ('DeletedClaim', 'lookup', 'lookup_deleted_claim', 'lookup_deleted_claim.assertion.1'),
                  ('DoubleMerge', 'mutant', 'slide_no_double_merge', 'slide_no_double_merge.assertion.1')]
    for module, source, entry, property_id in violations:
        path = HERE / 'Generated' / f'{module}.lean'
        run(TOOLS['goto-lean'], WORK / f'{source}-checked.gb', '--function', entry,
            '-o', path)
        strings = [json.loads(s) for s in re.findall(r'"(?:[^"\\]|\\.)*"', path.read_text())]
        candidates = set(s for s in strings if f'; property {property_id};' in s)
        assert len(candidates) == 1, (property_id, candidates)
        name = module[0].lower() + module[1:]
        sites += f'def {name} : GotoLean.Site := {json.dumps(candidates.pop())}\n'
    (HERE / 'Generated/Sites.lean').write_text(sites + 'end ViolationSites\n')
    run('lake', 'build', 'Generated', 'Proofs.Init')

    rng = random.Random(2048)
    named = [(b'', 4, 0), (b'{}', 4, 1), (b'[]', 4, 1), (b'{"a":1}', 4, 3),
             (b'[1,2]', 4, 3), (b'"hi"', 4, 1), (b'"', 4, -3), (b']', 4, -2),
             (b'"\\q"', 4, -2), (b'{}', 0, -1), (b'[1,2]', 2, -1), (b'truX', 4, 1)]
    json_rows = [(data, cap) for data, cap, _ in named]
    json_rows += [(bytes(rng.choice(b'{}[],:"\\012true ab\x00\xff') for _ in range(rng.randrange(9))),
                   rng.randrange(5)) for _ in range(256)]
    slides = [packed(xs) for xs in itertools.product(range(5), repeat=4)]
    slides += [packed(rng.choices(range(16), k=4)) for _ in range(512)]
    keys = [0, 4, 8, 12, 2**32-1] + [rng.getrandbits(32) for _ in range(256)]
    rows = [('json', packed(data), len(data), cap) for data, cap in json_rows]
    rows += [('slide', value, 0, 0) for value in slides]
    rows += [('lookup', key, 0, 0) for key in keys]
    inputs = ''.join(' '.join(map(str, row)) + '\n' for row in rows)
    (WORK / 'inputs.txt').write_text(inputs)

    sources = ['native.c', 'json.c', 'slide.c', 'lookup.c']
    outputs = {}
    for name, flags in [('O0', ['-O0']), ('O2', ['-O2']),
                        ('sanitized', ['-O1', '-g', '-fsanitize=address,undefined',
                                       '-fno-sanitize-recover=all', '-fno-omit-frame-pointer'])]:
        binary = WORK / name
        run(os.environ.get('CC', 'cc'), '-std=c11', *flags, *sources, '-o', binary)
        output = run(binary, input=inputs)
        outputs[name] = output
        (WORK / f'{name}.txt').write_text(output)
    bug = subprocess.run([str(WORK / 'sanitized')], cwd=HERE, input='slide 7967 0 0\n',
                         capture_output=True, text=True, timeout=30)
    (WORK / 'large-exponent-ubsan.txt').write_text(bug.stderr)
    assert bug.returncode != 0 and 'shift exponent 32' in bug.stderr, bug.stderr
    run(os.environ.get('CC', 'cc'), '-std=c11', '-O2', '-I', HERE,
        'native.c', 'json.c', wrapper, 'lookup.c', '-o', WORK / 'mutant-native')
    mutation = run(WORK / 'mutant-native', input='slide 131329 0 0\n')
    assert int(mutation) != slide_expected(131329), 'double-merge mutation survived'
    lean = run('lake', 'env', 'lean', '-j1', '-M1024', '--run', 'Run.lean', input=inputs)
    for name, output in outputs.items():
        assert len(output.splitlines()) == len(rows), name
        for row, native, model in zip(rows, output.splitlines(), lean.splitlines()):
            assert native == model, f'{name}: {row}: native {native}; Lean {model}'
    results = [list(map(int, line.split())) for line in lean.splitlines()]
    assert len(results) == len(rows)
    for i, (_, _, expected) in enumerate(named):
        assert results[i][0] == expected % 2**32, (named[i], results[i])
    assert results[2][4:8] == [2, 0, 2, 0], '[] token fields'
    for row, result in zip(rows, results):
        if row[0] == 'slide':
            assert result == [slide_expected(row[1])], (row, result)
        elif row[0] == 'lookup':
            assert result == [1 if row[1] == 4 else 3 if row[1] == 8 else 4], (row, result)
    accepted_invalid = []
    for (data, _), result in zip(json_rows, results):
        if result[0] < 2**31:
            try:
                json.loads(data)
            except (ValueError, UnicodeError):
                accepted_invalid.append(data.hex())
    (WORK / 'results.txt').write_text(lean)
    run('lake', 'env', 'lean', '-j1', '-M1024', 'Violations.lean')
    report = {'json_cases': len(json_rows), 'slide_cases': len(slides), 'lookup_cases': len(keys),
              'modes': ['native O0', 'native O2', 'ASan/UBSan', 'Lean'],
              'kernel_checked_violations': 4,
              'positive_contracts': ['JsmnProofs.initialize_completes'],
              'kernel_json_replay': 'bounds/arithmetic profile; full pointer-metadata replay exceeds 1 GiB',
              'tokenizer_accepts_non_JSON': sorted(set(accepted_invalid)),
              'scope': 'concrete executions with CBMC pointer checks; not a universal Lean proof'}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS {len(rows)} complete-result comparisons across four modes; '
          f'{len(accepted_invalid)} JSON grammar disagreements (tokenizer scope).')


if __name__ == '__main__':
    main()
