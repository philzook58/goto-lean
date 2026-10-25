#!/usr/bin/env python3
"""Prepare solution-free pi trials; retain prompts, tool traces and artifacts.

PI_CODING_AGENT_DIR should refer to a writable pi configuration, outside trials.
No credentials or provider configuration are copied into evaluation artifacts.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
TASKS = {
    'choice': ('bounded_pick', 'Prove and audit a named theorem completes: all '
               'executions admitted by the source assumption finish safely, '
               'with postcondition fun r => r.toNat < 16. Quantify all choices '
               'through finishes; do not replace it by one eval stream. Also '
               'add a checked feasible returned replay with explicit choices '
               'and explain their consumption.'),
    'complement': ('double_complement', 'Prove and audit a named theorem completes '
                   'for every 32-bit input: finishes with a sufficient block '
                   'bound and postcondition that the returned value equals '
                   'the input. This is a universal functional completion claim, '
                   'not just concrete runs or a run.wp theorem.'),
    'assume': ('add_small', 'Prove a named theorem completes: for every 32-bit x, '
               'the admitted executions finish and the return value has natural '
               'value x.toNat + 7. Keep the source assumption. The public theorem '
               'must state finishes with a sufficient bound, not just run.wp.'),
    'branch': ('cap_value', 'Prove a named theorem completes for all 32-bit x and '
               'limit and all choices: execution finishes and returns '
               '(if BitVec.ult x limit then x else limit). State finishes in '
               'the exported theorem and audit it.'),
    'fixed-loop': ('three_steps', 'Prove a named theorem completes for every '
                   '32-bit x: the function finishes safely and returns x + 3 '
                   'with bitvector wrapping. A finite block bound is appropriate '
                   'because the source loop has exactly three iterations. '
                   'Export a finishes theorem and audit it.'),
    'copy': ('copy_input', 'Prove for every 32-bit input and all admitted choices '
             'that the instrumented entry completes safely and returns its '
             'input. Export and audit a named completion theorem. This tests '
             'declaration effects, not just one replay.'),
    'replay': ('signed_pick', 'Add checked concrete executions for (3,2), (2,3), '
              '(2,2), (-3,-2), and (INT_MIN,INT_MAX). Check expected signed results '
              'and explain the choices consumed. Include a check that zero fuel '
              'does not count as completion.'),
    'prove': ('toggle_twice', 'Prove for every 32-bit x and mask, and every admitted '
              'nondeterministic choice, that the instrumented entry completes '
              'safely and returns x. Audit the theorem. Concrete samples alone '
              'are insufficient.'),
    'bug': ('wrong_pick', 'Find an input violating the C assertion. Prove a '
            'kernel-checked replay naming its exact property site, then derive '
            'an operational failed execution and refute run safety. Audit public '
            'claims. Do not repair or change the C.'),
    'loop': ('drain', 'Prove unbounded safety and return value zero for every '
             '32-bit input using a PC invariant. Audit the theorem. Explain '
             'that this is partial correctness. In this trial do not attempt '
             'termination or a rank: finish the requested invariant proof. '
             'A fixed-fuel sample is insufficient.'),
}


def prepare(destination, task, skill_source=None, guide_source=None, lean_skill=None):
    destination.mkdir(parents=True, exist_ok=False)
    # Only runtime implementation/proofs, no solved examples or previous trials.
    for name in ('GotoLean', 'tools'):
        shutil.copytree(ROOT / name, destination / name,
                        ignore=shutil.ignore_patterns('__pycache__'))
    for name in ('GotoLean.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
        shutil.copy2(ROOT / name, destination / name)
    # Copy runtime artifacts only; .lake can also contain unrelated test sources.
    shutil.copytree(ROOT / '.lake/build', destination / '.lake/build')
    (destination / 'build/bin').mkdir(parents=True)
    for name in ('goto-cc', 'goto-instrument', 'goto-lean'):
        shutil.copy2(ROOT / 'build/bin' / name, destination / 'build/bin' / name)
    (destination / 'docs').mkdir()
    shutil.copy2(guide_source or ROOT / 'docs/AGENT_GUIDE.md', destination / 'docs/AGENT_GUIDE.md')
    shutil.copytree(skill_source or ROOT / '.agents/skills/goto-lean',
                    destination / '.agents/skills/goto-lean',
                    ignore=shutil.ignore_patterns('__pycache__'))
    extra = ''
    if lean_skill:
        shutil.copytree(lean_skill, destination / '.agents/skills/lean4')
        extra = '''Also read and use .agents/skills/lean4/SKILL.md for Lean proof work.
This pi environment has no Lean LSP/MCP, slash commands, or plugin helper scripts.
Use Lean/Lake and installed Std sources; do not install mathlib or other tools.
'''
    shutil.copy2(Path(__file__).parent / 'tasks' / (task + '.c'), destination / 'task.c')
    function, request = TASKS[task]
    prompt = f'''Read .agents/skills/goto-lean/SKILL.md directly; that exact file exists.
Do not search the filesystem for the skill.
{extra}Work only in this isolated checkout. Do not search the internet or seek
solved examples. You may read the installed Lean standard-library sources
(locate them with lean --print-prefix) and use Lean/Lake. Other trial directories
and the original goto-lean checkout are off limits.
The checkout contains the runtime API but no example solutions.

Translate task.c with entry {function} into build/task, keeping C unchanged.
{request}
Keep handwritten work in build/task/Spec.lean. Compile that file and write
REPORT.md with the exact command, result, scope and any unresolved obligations.
Aim for at most 18 tool calls. If blocked, preserve your best attempt and report the
actual error. Do not add axioms, sorry, native_decide, or weaken the requested claim.
'''
    (destination / 'PROMPT.md').write_text(prompt)
    return prompt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('task', choices=TASKS)
    parser.add_argument('--out', type=Path, required=True,
                        help='fresh trial directory, preferably under /tmp')
    parser.add_argument('--run', action='store_true', help='contact pi/model after preparation')
    parser.add_argument('--model', default='openrouter/google/gemma-4-31b-it')
    parser.add_argument('--thinking', choices=['off', 'low', 'medium', 'high'], default='low')
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--skill-source', type=Path, help='alternative goto-lean skill for comparison')
    parser.add_argument('--guide-source', type=Path, help='alternative guide for comparison')
    parser.add_argument('--lean-skill', type=Path, help='additional Lean skill directory')
    parser.add_argument('--preload-guidance', action='store_true',
                        help='supply skill bodies directly in pi system context')
    parser.add_argument('--attempt-source', type=Path,
                        help='seed a repair trial with an earlier unsolved spec')
    args = parser.parse_args()
    destination = args.out.resolve()
    prompt = prepare(destination, args.task, args.skill_source, args.guide_source, args.lean_skill)
    if args.attempt_source:
        (destination / 'build/task').mkdir()
        shutil.copy2(args.attempt_source, destination / 'build/task/Spec.lean')
        prompt += '''\nSpec.lean contains your earlier failed attempt, not a solution.
Repair it without weakening its statement. After your first reduction, insert
trace_state and compile to read the real remaining goal. Do not infer the goal
from comments in the attempted proof. Remove obsolete tactics instead of adding
more unfolding when step is no longer present. Do not use simp only for the
initial reduction: it bypasses the starter's local effect-reduction rules.
'''
        (destination / 'PROMPT.md').write_text(prompt)
    hashes = {name: hashlib.sha256((destination / name).read_bytes()).hexdigest()
              for name in ('task.c', 'docs/AGENT_GUIDE.md', '.agents/skills/goto-lean/SKILL.md')}
    if args.lean_skill:
        hashes['.agents/skills/lean4/SKILL.md'] = hashlib.sha256(
            (destination / '.agents/skills/lean4/SKILL.md').read_bytes()).hexdigest()
    if args.attempt_source:
        hashes['seed_spec'] = hashlib.sha256(args.attempt_source.read_bytes()).hexdigest()
    hashes['tools/translate.py'] = hashlib.sha256((destination / 'tools/translate.py').read_bytes()).hexdigest()
    (destination / 'inputs.json').write_text(json.dumps(hashes, indent=2) + '\n')
    print(destination, flush=True)
    if not args.run:
        return
    command = ['pi', '--offline', '--no-extensions', '--no-mcp', '--no-skills',
               '--no-context-files', '--no-session', '--no-prompt-templates',
               '--model', args.model, '--thinking', args.thinking, '--mode', 'json',
               '--tools', 'read,bash,edit,write', '-p', prompt]
    if args.preload_guidance:
        command[1:1] = ['--append-system-prompt', str(destination / '.agents/skills/goto-lean/SKILL.md')]
        if args.lean_skill:
            command[1:1] = ['--append-system-prompt', str(destination / '.agents/skills/lean4/SKILL.md')]
    start = time.monotonic()
    with (destination / 'trace.jsonl').open('w') as stdout, \
            (destination / 'stderr.txt').open('w') as stderr:
        process = subprocess.Popen(command, cwd=destination, stdout=stdout,
                                   stderr=stderr, start_new_session=True)
        try:
            code = process.wait(timeout=args.timeout)
            timed_out = False
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            code, timed_out = process.returncode, True
    metadata = dict(task=args.task, model=args.model, exit_code=code,
                    preloaded_guidance=args.preload_guidance,
                    seeded_attempt=bool(args.attempt_source),
                    thinking=args.thinking,
                    timed_out=timed_out, seconds=round(time.monotonic() - start, 1),
                    input_sha256=hashes,
                    c_unchanged=hashes['task.c'] == hashlib.sha256(
                        (destination / 'task.c').read_bytes()).hexdigest())
    spec = destination / 'build/task/Spec.lean'
    if spec.is_file():
        # pi exiting successfully does not mean its proof compiles.
        with (destination / 'verification.txt').open('w') as output:
            try:
                checked = subprocess.run(
                    ['lake', '-d', str(spec.parent), 'lean', str(spec), '--', '-j1', '-M1024'],
                    cwd=destination, stdout=output, stderr=subprocess.STDOUT, timeout=60)
                metadata['spec_compile_exit_code'] = checked.returncode
            except subprocess.TimeoutExpired:
                metadata['spec_compile_timed_out'] = True
    (destination / 'run.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(json.dumps(metadata), flush=True)


if __name__ == '__main__':
    main()
