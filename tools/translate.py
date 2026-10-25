#!/usr/bin/env python3
"""Compile one C translation unit into a Lean model and a handwritten spec starter."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECKS = ['pointer-check', 'bounds-check', 'signed-overflow-check',
          'div-by-zero-check', 'undefined-shift-check', 'conversion-check']


def run(*args, **kwargs):
    command = list(map(str, args))
    return subprocess.run(command, check=True, capture_output=True, text=True, **kwargs)


def example_call(model, namespace):
    # Read the printer's small, fixed eval header, not the original C syntax.
    header = re.search(r'^def eval(.*?) :\n', model, re.MULTILINE | re.DOTALL).group(1)
    parameters = re.findall(r'\((\w+) :', header)
    values = ['1000' if name == 'fuel' else '[]' if name == 'choices' else 'default'
              for name in parameters]
    call = namespace + '.eval ' + ' '.join(values)
    binders = ' '.join(header.split('(fuel : Nat)', 1)[0].split())
    values = ['10' if name == 'fuel' else '[]' if name == 'choices' else
              'default' if name == 'memory' else name for name in parameters]
    symbolic = namespace + '.eval ' + ' '.join(values)
    goal = f'''example {binders} :
    ({symbolic}).fst = .returned YOUR_EXPECTED_RESULT := by
  simp <;> bv_decide'''
    arguments = ' '.join('default' if name == 'memory' else name
                         for name in parameters if name not in ('fuel', 'choices'))
    spec = f'''theorem completes {binders} :
    finishes {namespace}.step 10 ({namespace}.initial {arguments})
      (fun result ↦ result = YOUR_EXPECTED_RESULT) := by
  simp [finishes, {namespace}.step, {namespace}.initial, Bind.bind,
    Action.wp_bind, choose, check, assume, Action.wp, Pure.pure, Sum.elim]
  -- Inspect remaining goals; use kernel-checkable rewrites/arithmetic reasoning.'''
    return call, goal, spec


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--function', required=True, help='C entry function to translate')
    parser.add_argument('--out', type=Path, default=ROOT / 'build/try',
                        help='dedicated output directory (default: build/try)')
    parser.add_argument('--build-dir', type=Path, default=ROOT / 'build',
                        help='CMake build directory containing bin/goto-*')
    parser.add_argument('--cc-arg', action='append', default=[], metavar='ARG',
                        help='extra goto-cc argument; repeat as --cc-arg=-I/path')
    args = parser.parse_args()
    source, out = args.source.resolve(), args.out.resolve()
    binaries = args.build_dir.resolve() / 'bin'
    if not source.is_file():
        parser.error(f'no source file: {source}')
    for name in ('goto-cc', 'goto-instrument', 'goto-lean'):
        if not (binaries / name).is_file():
            parser.error(f'missing {binaries / name}; build goto-lean-tools first')
    out.mkdir(parents=True, exist_ok=True)

    # Publish generated files only after translation and Lean compilation succeed.
    # Spec.lean belongs to the user and is never regenerated. Lean only compiles files
    # inside the Lake root, so an output directory elsewhere is staged under build/.
    staging = out if out.is_relative_to(ROOT) else ROOT / 'build'
    staging.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.translate-', dir=staging) as temporary:
        work = Path(temporary)
        raw, checked = work / 'raw.gb', work / 'checked.gb'
        print(f'Compiling {source} and inserting safety checks...', flush=True)
        run(binaries / 'goto-cc', '-std=c11', *args.cc_arg, '-c', source, '-o', raw)
        run(binaries / 'goto-instrument', *('--' + flag for flag in CHECKS), raw, checked)
        result = run(binaries / 'goto-instrument', '--show-properties', '--json-ui',
                     checked)
        properties = [prop for entry in json.loads(result.stdout)
                      for prop in entry.get('properties', [])]
        inventory = '\n'.join(f"{p['name']}: {p['description']}" for p in properties)
        (work / 'properties.txt').write_text(inventory + '\n')
        print(f'\n{len(properties)} properties in the instrumented translation unit '
              '(not a proved or entry-reachable count):', flush=True)
        print(inventory or 'ZERO properties. Add C assertions or a Lean requirement.', flush=True)
        print(f'\nTranslating {args.function} and type-checking Model.lean...', flush=True)
        run(binaries / 'goto-lean', checked, '--function', args.function,
            '-o', work / 'Model.lean')
        model = (work / 'Model.lean').read_text()
        namespace = re.search(r'^namespace (\S+)$', model, re.MULTILINE).group(1)
        call, bounded_goal, spec_goal = example_call(model, namespace)
        run('lake', 'env', 'lean', '-j1', '-M1024', '-o', work / 'Model.olean',
            work / 'Model.lean', cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS='1'))
        for name in ('raw.gb', 'checked.gb', 'properties.txt', 'Model.lean', 'Model.olean'):
            shutil.move(work / name, out / name)

    # A local Lake project makes imports work in editors as well as the terminal.
    if not any((out / name).exists() for name in ('lakefile.toml', 'lakefile.lean')):
        dependency = json.dumps(os.path.relpath(ROOT, out))
        (out / 'lakefile.toml').write_text(f'''name = "translatedExample"
defaultTargets = ["Model"]

[[require]]
name = "gotoLean"
path = {dependency}

[[lean_lib]]
name = "Model"
''')
    if not (out / 'lean-toolchain').exists():
        (out / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())

    spec = out / 'Spec.lean'
    if not spec.exists():
        spec.write_text(f'''import Model
import Std.Tactic.BVDecide
import GotoLean.Termination
import GotoLean.Audit

open GotoLean
set_option autoImplicit false

-- Intended behavior and preconditions:

section ExampleRuns
#check {namespace}.eval
-- Set representative inputs, choices and memory; add #guard checks for expected outcomes.
#eval ({call}).fst
end ExampleRuns

section BoundedExec
attribute [local simp] {namespace}.eval {namespace}.step {namespace}.initial
  evalLoop Action.eval Action.bind Bind.bind Pure.pure

/-
{bounded_goal}
- Exploration only: bv_decide can introduce native axioms rejected by #check_axioms.
-/
end BoundedExec

section Specs
-- Reduce generated blocks and effects before solving the remaining pure goals.
attribute [local simp] {namespace}.step {namespace}.initial
  finishes Bind.bind Action.wp_bind choose check assume Action.wp Pure.pure Sum.elim

/-
Edit the completion bound; loops may need an invariant instead.
{spec_goal}

#check_axioms completes
-/
end Specs
''')
        print(f'\nCreated {spec}', flush=True)
    else:
        print(f'\nKept existing {spec}', flush=True)
    print('Model type-checked. No C assertions or handwritten spec have been proved.')
    print(f'Default-input example: #eval ({call}).fst')
    print('Next: open Spec.lean in your editor, or check it with:')
    print(shlex.join(['lake', '-d', str(out), 'lean', str(spec), '--', '-j1', '-M1024']))


if __name__ == '__main__':
    try:
        main()
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f'translate: {error}', file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout or '', end='', file=sys.stderr)
            print(error.stderr or '', end='', file=sys.stderr)
        sys.exit(1)
