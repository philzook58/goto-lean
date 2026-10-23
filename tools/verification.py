#!/usr/bin/env python3
"""Generate, check, and recheck a local verification receipt. Standard library only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
WORK = Path('.lake/verification')


def run(args, *, env=None):
    result = subprocess.run(list(map(str, args)), env=env, capture_output=True, check=True,
                            timeout=120)
    return result.stdout


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def hashes(paths):
    return {str(p): digest(p.read_bytes()) for p in sorted(set(paths))}


def same(expected, actual, label):
    if expected != actual:
        changed = ''
        if isinstance(expected, dict) and isinstance(actual, dict):
            keys = sorted(set(expected) | set(actual))
            changed = ': ' + ', '.join(k for k in keys if expected.get(k) != actual.get(k))
        raise ValueError(f'{label} changed{changed}; regenerate/recheck before using this result')


def inventory(instrument, binary):
    messages = json.loads(run([instrument, '--json-ui', '--show-properties', binary]))
    return sorted((p for m in messages for p in m.get('properties', [])), key=lambda p: p['name'])


def counts(properties):
    result = {}
    for prop in properties:
        function = prop['sourceLocation']['function']
        classes = result.setdefault(function, {})
        classes[prop['class']] = classes.get(prop['class'], 0) + 1
    return result


def preprocess(policy, cc):
    return run([cc, *policy['compile'], '-E', policy['source']])


def inputs(policy, config, tools):
    text = preprocess(policy, tools['goto-cc']['path'])
    paths = [Path(policy['source']), config, Path(__file__).resolve()]
    for name in re.findall(rb'^#\s+\d+\s+("(?:[^"\\]|\\.)*")', text, re.M):
        path = Path(json.loads(name))
        if path.is_file():
            paths.append(path)
    return {'files': hashes(paths), 'preprocessed_sha256': digest(text), 'tools': tools}, text


def tool_info():
    result = {}
    for name, variable in [('goto-cc', 'GOTO_CC'), ('goto-instrument', 'GOTO_INSTRUMENT'),
                           ('goto-lean', 'GOTO_LEAN')]:
        path = Path(os.environ.get(variable, str(ROOT / 'build/bin' / name))).resolve()
        result[name] = {'path': str(path), 'sha256': digest(path.read_bytes()),
                        'version': run([path, '--version']).decode().strip()}
    result['lean'] = {'version': run(['lake', 'env', 'lean', '--version']).decode().strip()}
    result['lake'] = {'version': run(['lake', '--version']).decode().strip()}
    prefix = Path(run(['lake', 'env', 'lean', '--print-prefix']).decode().strip())
    for name in ['lean', 'lake']:
        result[name]['sha256'] = digest((prefix / 'bin' / name).read_bytes())
    return result


def artifacts(policy):
    paths = [WORK / 'input.i', WORK / 'raw.gb', WORK / 'checked.gb', WORK / 'properties.json']
    return hashes(paths + [Path(e['lean']) for e in policy['entries']])


def proof_inputs():
    # Conservative dependency set: all local example Lean and all runtime/proof-library sources.
    paths = [p for p in Path('.').rglob('*.lean') if '.lake' not in p.parts]
    paths += list((ROOT / 'GotoLean').rglob('*.lean')) + [ROOT / 'GotoLean.lean']
    for base in [Path('.'), ROOT]:
        paths += [p for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
                  if (p := base / name).exists()]
    return hashes(paths)


def compiled_inputs():
    paths = []
    for base in [ROOT / '.lake/build/lib/lean', Path('.lake/build/lib/lean'), WORK]:
        paths += [p for p in base.rglob('*.olean*') if p.is_file()]
    return hashes(paths + ([WORK / 'Audit.lean'] if (WORK / 'Audit.lean').exists() else []))


def validate(policy, config, tools, generated):
    current, _ = inputs(policy, config, tools)
    same(generated['inputs'], current, 'source/configuration/tool identity')
    same(generated['artifacts'], artifacts(policy), 'generated artifact')
    props = inventory(tools['goto-instrument']['path'], WORK / 'checked.gb')
    same(policy['expected_properties'], counts(props), 'expected property inventory')
    same(generated['properties'], props, 'GOTO property inventory')


def generate(policy, config, tools):
    (WORK / 'generated.json').unlink(missing_ok=True)
    before, text = inputs(policy, config, tools)
    (WORK / 'input.i').write_bytes(text)
    run([tools['goto-cc']['path'], *policy['compile'], '-c', WORK / 'input.i',
         '-o', WORK / 'raw.gb'])
    run([tools['goto-instrument']['path'], *policy['checks'],
         WORK / 'raw.gb', WORK / 'checked.gb'])
    props = inventory(tools['goto-instrument']['path'], WORK / 'checked.gb')
    same(policy['expected_properties'], counts(props), 'expected property inventory')
    save(WORK / 'properties.json', props)
    entries = []
    for entry in policy['entries']:
        path = Path(entry['lean'])
        path.parent.mkdir(parents=True, exist_ok=True)
        run([tools['goto-lean']['path'], WORK / 'checked.gb', '--function', entry['function'],
             '-o', path])
        emitted = sorted(set(re.findall(r'\bcheck\s+"[^"\n]*; property ([^;]+);', path.read_text())))
        functions = entry.get('functions', [entry['function']])
        expected = {p['name'] for p in props if p['sourceLocation']['function'] in functions}
        if set(emitted) != expected:
            raise ValueError(f'{path}: emitted properties differ from the declared function/callee scope')
        entries.append({**entry, 'properties': emitted})
    after, _ = inputs(policy, config, tool_info())
    same(before, after, 'inputs during generation')
    save(WORK / 'generated.json', {'inputs': before, 'artifacts': artifacts(policy),
                                  'properties': props, 'entries': entries})
    print(f'Generated {len(entries)} entries; {len(props)} actual GOTO properties. Not yet proved.')


def report(policy, config):
    print('Entry | Evidence | Imported properties | Result')
    for entry in policy['entries']:
        functions = entry.get('functions', [entry['function']])
        total = sum(sum(policy['expected_properties'].get(f, {}).values()) for f in functions)
        print(f"{entry['function']} | {entry['scope']} | {total} | {entry['summary']}")
        if entry.get('requires'):
            print('  Requires: ' + entry['requires'])
    if any(e['scope'] != 'unbounded' for e in policy['entries']):
        print('Execution/counterexample rows concern specific inputs and reached checks only.')
    print('Lean model proofs; correspondence to C remains unproved.')
    print(f'Reviewed statements and inputs: {config}; receipt: {WORK / "result.json"}')


def check(policy, config, tools, generated):
    validate(policy, config, tools, generated)
    before = proof_inputs()
    run(['lake', 'build', *policy['build']])
    env = dict(os.environ, LEAN_PATH=str(WORK.resolve()) + os.pathsep + os.environ.get('LEAN_PATH', ''))
    for module in policy['proofs']:
        output = WORK / (module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        run(['lake', 'env', 'lean', '-j1', '-M1024', '-o', output,
             module.replace('.', '/') + '.lean'], env=env)
    claims = [e['claim'] for e in policy['entries']]
    audit = '\n'.join('import ' + m for m in ['GotoLean.Audit', *policy['proofs']])
    for i, entry in enumerate(policy['entries']):
        audit += f"\ndef certified_{i} : {entry['statement']} := {entry['claim']}\n"
        audit += f'#check_axioms certified_{i}\n'
    (WORK / 'Audit.lean').write_text(audit)
    run(['lake', 'env', 'lean', '-j1', '-M1024', WORK / 'Audit.lean'], env=env)
    validate(policy, config, tool_info(), generated)
    same(before, proof_inputs(), 'proof/model inputs during checking')
    save(WORK / 'result.json', {'kind': 'checked local receipt',
                               'evidence': 'Lean proofs of reviewed statements and axiom audits; excludes replay/native/CBMC results',
                               'scope_source': 'reviewed policy; not inferred from theorem types',
                               'generated': generated,
                               'proof_inputs': before, 'compiled_inputs': compiled_inputs(), 'policy': policy,
                               'claims': claims, 'axioms_allowed': ['propext', 'Quot.sound', 'Classical.choice']})
    report(policy, config)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['generate', 'check', 'status'])
    parser.add_argument('config', nargs='?', default='verification.json')
    args = parser.parse_args()
    WORK.mkdir(parents=True, exist_ok=True)
    if args.mode != 'status':
        (WORK / 'result.json').unlink(missing_ok=True)
    config = Path(args.config)
    policy = json.loads(config.read_text())
    entries = policy['entries']
    if not entries or not policy['proofs'] or any(
            not e['claim'] or not e['statement'] or not e['summary'] for e in entries):
        raise ValueError('each entry needs a claim, expected statement, summary and proof module')
    if any(e['scope'] not in ['unbounded', 'execution', 'counterexample'] for e in entries):
        raise ValueError('scope must be unbounded, execution, or counterexample (reviewed, not inferred)')
    if len({e['lean'] for e in entries}) != len(entries):
        raise ValueError('entries must have distinct generated Lean paths')
    tools = tool_info()
    if args.mode == 'generate':
        generate(policy, config, tools)
    elif args.mode == 'check':
        check(policy, config, tools, json.loads((WORK / 'generated.json').read_text()))
    else:
        result = json.loads((WORK / 'result.json').read_text())
        validate(policy, config, tools, result['generated'])
        same(result['policy'], policy, 'claim policy')
        same(result['proof_inputs'], proof_inputs(), 'proof/model inputs')
        same(result['compiled_inputs'], compiled_inputs(), 'compiled Lean artifacts')
        report(policy, config)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout.decode(errors='replace'), file=sys.stderr)
            print(error.stderr.decode(errors='replace'), file=sys.stderr)
        raise SystemExit(f'verification: {error}')
