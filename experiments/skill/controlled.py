#!/usr/bin/env python3
"""Frozen, interleaved comparison of compact guidance with selected Lean notes."""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import signal
import subprocess
import time
import evaluate

BASE = Path('/tmp/goto-lean-controlled')
ROOT = evaluate.ROOT
MODEL = 'openrouter/google/gemma-4-31b-it'
TASKS = ['complement', 'choice', 'branch']
TIMEOUT = 180

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def protected(directory):
    files = []
    for name in ['GotoLean', 'tools']:
        files += [p for p in (directory / name).rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    files += [directory / n for n in ['task.c', 'GotoLean.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'build/task/Model.lean']]
    return {str(p.relative_to(directory)): digest(p) for p in sorted(files)}

def contract(task):
    if task == 'complement':
        return '''theorem controller_contract (x : BitVec 32) :
  ∃ fuel, finishes v_double_complement.step fuel (v_double_complement.initial x)
    (fun r => r = x) := ⟨_, completes x⟩\n'''
    if task == 'choice':
        return '''theorem controller_contract :
  ∃ fuel, finishes v_bounded_pick.step fuel v_bounded_pick.initial
    (fun r => r.toNat < 16) := ⟨_, completes⟩\n'''
    return '''theorem controller_contract (x limit : BitVec 32) :
  ∃ fuel, finishes v_cap_value.step fuel (v_cap_value.initial x limit)
    (fun r => r = if BitVec.ult x limit then x else limit) := ⟨_, completes x limit⟩\n'''

def prepare():
    BASE.mkdir(exist_ok=False)
    selected = BASE / 'selected-lean'
    shutil.copytree('/tmp/goto-lean-round2/selected-lean', selected)
    # Make choice's single primary endpoint comparable with the other tasks.
    evaluate.TASKS['choice'] = ('bounded_pick',
        'Prove and audit a named theorem completes: all executions admitted by '
        'the source assumption finish safely, with postcondition fun r => r.toNat < 16. '
        'Quantify all choices through finishes; do not replace it by one eval stream. '
        'The public theorem must state finishes with a sufficient block bound.')
    order = [(task, arm, repeat) for task in TASKS for arm in ['compact', 'selected'] for repeat in range(1, 4)]
    random.Random(20261024).shuffle(order)
    trials = []
    for task, arm, repeat in order:
        name = f'{task}-{arm}-{repeat}'
        directory = BASE / name
        prompt = evaluate.prepare(directory, task, lean_skill=selected if arm == 'selected' else None)
        common = (directory / '.agents/skills/goto-lean/SKILL.md').read_text()
        system = common + ('\n\n' + (selected / 'SKILL.md').read_text() if arm == 'selected' else '')
        (directory / 'SYSTEM.md').write_text(system)
        function = evaluate.TASKS[task][0]
        subprocess.run(['python3', 'tools/translate.py', 'task.c', '--function', function, '--out', 'build/task'], cwd=directory, check=True, stdout=subprocess.DEVNULL)
        hashes = protected(directory)
        hashes['docs/AGENT_GUIDE.md'] = digest(directory / 'docs/AGENT_GUIDE.md')
        hashes['.agents/skills/goto-lean/SKILL.md'] = digest(directory / '.agents/skills/goto-lean/SKILL.md')
        hashes['SYSTEM.md'] = digest(directory / 'SYSTEM.md')
        hashes['PROMPT.md'] = digest(directory / 'PROMPT.md')
        (directory / 'inputs.json').write_text(json.dumps(hashes, indent=2))
        trials.append(dict(name=name, task=task, arm=arm, repeat=repeat, inputs=hashes))
    protocol = dict(model=MODEL, thinking='low', timeout_seconds=TIMEOUT, concurrency=3,
        repeats=3, tasks=TASKS, order_seed=20261024,
        max_output_tokens_per_response=8192,
        infrastructure_amendment='Initial launch returned only 402 credit/max_tokens errors, with zero generated content. Restarted all fresh trials with one common 8192 output-token cap.',
        intervention='One combined preloaded system guidance file: compact skill versus identical skill plus selected Lean notes; selected arm also has notes file and read instruction.',
        primary_endpoint='Original model/runtime/C unchanged; final Spec compiles; public completes directly states finishes; exact requested input/postcondition adapter compiles and both claims pass axiom audit. Arbitrary sufficient fuel allowed.',
        choice_scope='Completion only; replay secondary request removed before all trials.',
        restrictions='Fresh attempts, no solutions, no repairs, no mid-study changes, installed Std sources permitted.',
        caveats='No provider seed; concurrency and provider timing vary; three repeats per cell are exploratory.',
        harness_sha256=digest(Path(__file__)), checker_sha256=digest(ROOT / '.agents/skills/goto-lean/scripts/check_spec.py'),
        trials=trials)
    (BASE / 'protocol.json').write_text(json.dumps(protocol, indent=2) + '\n')
    shutil.copy2(__file__, BASE / 'controlled.py')
    print(f'Frozen {len(trials)} trials: {BASE / "protocol.json"}', flush=True)


def run(trial):
    directory = BASE / trial['name']
    command = ['pi', '--append-system-prompt', str(directory / 'SYSTEM.md'), '--offline', '--no-extensions', '--no-mcp', '--no-skills', '--no-context-files', '--no-session', '--no-prompt-templates', '--model', MODEL, '--thinking', 'low', '--mode', 'json', '--tools', 'read,bash,edit,write', '-p', (directory / 'PROMPT.md').read_text()]
    start = time.monotonic()
    with (directory / 'trace.jsonl').open('w') as stdout, (directory / 'stderr.txt').open('w') as stderr:
        process = subprocess.Popen(command, cwd=directory, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            code = process.wait(timeout=TIMEOUT)
            timeout = False
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            code, timeout = process.returncode, True
    result = dict(name=trial['name'], task=trial['task'], arm=trial['arm'], repeat=trial['repeat'], exit_code=code, timed_out=timeout, seconds=round(time.monotonic()-start, 1))
    result['changed_protected_files'] = [name for name, value in trial['inputs'].items() if not (directory / name).is_file() or digest(directory / name) != value]
    spec = directory / 'build/task/Spec.lean'
    result['passed'] = False
    if spec.is_file():
        # Controller-only adapter is added after the agent has exited, never in its prompt.
        graded = spec.parent / 'ControllerGrade.lean'
        graded.write_text(spec.read_text() + '\nopen GotoLean\n' + contract(trial['task']))
        check = ['python3', str(ROOT / '.agents/skills/goto-lean/scripts/check_spec.py'), '--project', str(spec.parent), '--spec', graded.name, '--completion-claim', 'completes', '--claim', 'controller_contract']
        with (directory / 'grading.txt').open('w') as log:
            try:
                grade = subprocess.run(check, cwd=directory, stdout=log, stderr=subprocess.STDOUT, timeout=60)
                result['grade_exit_code'] = grade.returncode
                result['passed'] = grade.returncode == 0 and not result['changed_protected_files']
            except subprocess.TimeoutExpired:
                result['grade_timed_out'] = True
    (directory / 'run.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
    return result

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['prepare']:
        prepare()
    elif sys.argv[1:] == ['run']:
        protocol = json.loads((BASE / 'protocol.json').read_text())
        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            results = list(pool.map(run, protocol['trials']))
        (BASE / 'summary.json').write_text(json.dumps(results, indent=2) + '\n')
    else:
        raise SystemExit('usage: controlled.py prepare|run')
