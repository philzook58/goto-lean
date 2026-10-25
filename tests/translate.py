#!/usr/bin/env python3
"""Exercise the wrapper on real C: examples, failed assertions, reruns and failed translation."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BUILD = Path(sys.argv[1]).resolve()


def run(*command, code=0, **kwargs):
    result = subprocess.run(list(map(str, command)), cwd=ROOT, capture_output=True,
                            text=True, timeout=90, **kwargs)
    assert result.returncode == code, result.stdout + result.stderr
    return result.stdout


with tempfile.TemporaryDirectory(prefix='wrapper ', dir=BUILD) as temporary:
    work = Path(temporary)
    source, out = work / 'input.c', work / 'output'
    command = [sys.executable, ROOT / 'tools/translate.py', source,
               '--function', 'mymax', '--out', out, '--build-dir', BUILD,
               '--cc-arg=-DWRAPPER_TEST=1']
    source.write_text('''#ifndef WRAPPER_TEST
#error missing compiler argument
#endif
int mymax(int x, int y) { return x > y ? x : y; }
''')
    report = run(*command)
    assert 'ZERO properties' in report
    assert all((out / name).is_file() for name in
               ('raw.gb', 'checked.gb', 'properties.txt', 'Model.lean', 'Model.olean',
                'Spec.lean', 'lakefile.toml', 'lean-toolchain'))
    spec = out / 'Spec.lean'
    assert '#eval (v_mymax.eval default default 1000 []).fst' in spec.read_text()
    spec.write_text(spec.read_text() + '''
#guard (v_mymax.eval 3 2 10).1 == .returned 3
#guard (v_mymax.eval (.ofInt 32 (-3)) (.ofInt 32 (-2)) 10).1 ==
  .returned (.ofInt 32 (-2))
#guard (v_mymax.eval 42 43 10 []).fst.getValue? == some 43
''')
    spec.write_text(spec.read_text().replace('\nend BoundedExec', '''
example (x y : BitVec 32) :
    (v_mymax.eval x y 2 []).fst =
      .returned (if BitVec.slt y x then x else y) := by
  simp <;> bv_decide
end BoundedExec'''))
    spec.write_text(spec.read_text().replace('\nend Specs', '''
example (x y : BitVec 32) :
    (v_mymax.run x y).wp (fun result ↦ result = if BitVec.slt y x then x else y) := by
  apply finishes_run v_mymax.step 2
  simp [finishes, v_mymax.step, v_mymax.initial, Action.wp, Pure.pure] <;> rfl
end Specs'''))
    expected = spec.read_bytes()
    # Exercise the editor's import setup without the wrapper's former LEAN_PATH workaround.
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    env.pop('LEAN_PATH', None)
    setup = run('lake', '-d', out, 'setup-file', spec, env=env)
    assert '"Model"' in setup
    run('lake', '-d', out, 'lean', spec, '--', '-j1', '-M1024', env=env)
    # The same setup must expose a counterexample to a mistaken comparison.
    wrong = out / 'Wrong.lean'
    wrong.write_text(spec.read_text().replace('BitVec.slt y x', 'BitVec.slt x y'))
    report = run('lake', '-d', out, 'lean', wrong, '--', '-j1', '-M1024', env=env, code=1)
    assert 'The prover found a counterexample' in report
    typo = out / 'Typo.lean'
    typo.write_text(spec.read_text() + '\nexample : (1 : Nat) = accidentalResult := by rfl\n')
    report = run('lake', '-d', out, 'lean', typo, '--', '-j1', '-M1024', env=env, code=1)
    assert 'Unknown identifier `accidentalResult`' in report
    config = out / 'lakefile.toml'
    config.write_text(config.read_text() + '\n# handwritten project settings\n')
    expected_config = config.read_bytes()
    run(*command)
    assert spec.read_bytes() == expected, 'rerun overwrote handwritten spec'
    assert config.read_bytes() == expected_config, 'rerun overwrote project settings'

    # Type-checking a translation is allowed to succeed for buggy C.
    source.write_text('''int bad(int x, int y) {
      __CPROVER_assert(x >= y, "deliberately false for some inputs"); return x;
    }
    int mymax(int x, int y) { return bad(x, y); }\n''')
    report = run(*command)
    assert '1 properties' in report and 'bad.assertion.1' in report
    assert 'Default-input example: #eval (v_mymax.eval default default 1000 [] default).fst' in report
    assert spec.read_bytes() == expected
    # A fresh starter for a program with calls exercises default memory as well.
    fresh = work / 'with-memory'
    fresh_command = command.copy()
    fresh_command[fresh_command.index('--out') + 1] = fresh
    run(*fresh_command)
    run('lake', '-d', fresh, 'lean', fresh / 'Spec.lean', '--', '-j1', '-M1024', env=env)
    probe = out / 'Probe.lean'
    probe.write_text('''import Model
#guard match (v_mymax.eval 1 2 100 (List.replicate 20 0)).1 with
  | .assertionFailed _ => true
  | _ => false
''')
    run('lake', '-d', out, 'lean', probe, '--', '-j1', '-M1024', env=env)
    # The user's old examples now fail; the wrapper never claims to check them.
    run('lake', '-d', out, 'lean', spec, '--', '-j1', '-M1024', env=env, code=1)

    previous = (out / 'Model.lean').read_bytes()
    source.write_text('int mymax(int x, int y) { return missing syntax; }\n')
    run(*command, code=1)
    assert (out / 'Model.lean').read_bytes() == previous
    assert spec.read_bytes() == expected
    assert not list(out.glob('.translate-*')), 'temporary output was not cleaned up'

print('PASS wrapper: real C/Lean examples, bug outcome, preserved spec and failed regeneration')
