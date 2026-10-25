#!/usr/bin/env python3
"""Build real GOTO objects, check Lean proofs, and compare execution with native C."""
import argparse
import ctypes
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(args, *, env=None, ok=True):
    result = subprocess.run([str(x) for x in args], cwd=ROOT, env=env,
                            text=True, capture_output=True, timeout=120)
    if ok and result.returncode:
        raise RuntimeError(f"{' '.join(map(str, args))}\n{result.stdout}{result.stderr}")
    return result


def module(name):
    return ''.join(word.capitalize() for word in name.split('_'))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--printer', type=Path, required=True)
    parser.add_argument('--goto-cc', type=Path, required=True)
    parser.add_argument('--ir', type=Path)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(work))
    run([args.lake, 'build'])
    run([args.lake, 'env', 'lean', 'tests/Semantics.lean'])
    run([args.lake, 'env', 'lean', '-o', work / 'AuditHelper.olean',
         ROOT / 'tests/AuditHelper.lean'])
    run([args.lake, 'env', 'lean', ROOT / 'tests/Audit.lean'], env=env)
    print('PASS axiom gate: clean claims accepted; imported axioms, sorry and typos rejected', flush=True)
    obj = work / 'scalars.gb'
    run([args.goto_cc, '-D__CPROVER__', '-c', ROOT / 'tests/scalars.c', '-o', obj])
    u32, i32 = ctypes.c_uint32, ctypes.c_int32
    u8, i8, u64 = ctypes.c_uint8, ctypes.c_int8, ctypes.c_uint64
    # name, C arguments, C return type, Lean bit width, declaration choice stream
    specs = [
        ('increment', [u32], u32, 32, []),
        ('maximum', [u32, u32], u32, 32, []),
        ('countdown', [u32], u32, 32, []),
        ('narrow', [u8, u8], u8, 8, []),
        ('mix', [u32, u32], u32, 32, []),
        ('signed_cast', [i8], u32, 32, []),
        ('signed_compare', [i32, i32], u32, 32, []),
        ('shift', [u32, u32], u32, 32, []),
        ('arithmetic_shift', [i32, u32], i32, 32, []),
        ('quotient', [i32, i32], i32, 32, []),
        ('remainder', [i32, i32], i32, 32, []),
        ('unsigned_quotient', [u32, u32], u32, 32, []),
        ('unsigned_remainder', [u32, u32], u32, 32, []),
        ('wide', [u64, u64], u64, 64, []),
        ('array_read', [u32], u32, 32, [0]),
        ('string_local', [u32], u32, 32, [0]),
        ('array_write', [u32, u32], u32, 32, [0]),
        ('record_update', [u32, u32], u32, 32, [0]),
        ('nested_update', [u32, u32], u32, 32, [0]),
        ('union_update', [u32], u32, 32, [0]),
        ('enum_compare', [i32], u32, 32, [0]),
        ('local_loop', [u32], u32, 32, [0]),
        ('shadow', [u32], u32, 32, [0, 0]),
        ('logical', [ctypes.c_bool, ctypes.c_bool], ctypes.c_bool, 8, []),
        ('select_effect', [u32, u32], u32, 32, []),
        ('irreducible', [u32, u32], u32, 32, []),
    ]
    names = [s[0] for s in specs] + ['bad', 'pruned', 'constrained', 'uninitialized', 'bad_spin', 'self_read', 'read_before_write']
    for name in names:
        path = work / f'{module(name)}.lean'
        run([args.printer, obj, '--function', name, '-o', path])
        text = path.read_text()
        assert 'tests/scalars.c' in text and '-- ' in text
        run([args.lake, 'env', 'lean', '-o', path.with_suffix('.olean'), path], env=env)
        run([args.printer, obj, '--function', name, '-o', work / 'repeat.lean'])
        assert text == (work / 'repeat.lean').read_text(), 'nondeterministic printer output'
    print(f'PASS {len(names)} generated modules type-check and reproduce', flush=True)

    native = work / 'native.so'
    run(['cc', '-shared', '-fPIC', '-O2', ROOT / 'tests/scalars.c', '-o', native])
    lib = ctypes.CDLL(str(native))
    rng = random.Random(0x60704EA)
    runner = ['import ' + module(name) for name in names]
    runner += ['open GotoLean']
    expected = []
    for name, argtypes, restype, bits, choices in specs:
        fn = getattr(lib, name)
        fn.argtypes, fn.restype = argtypes, restype
        cases = []
        for _ in range(90):
            values = []
            for ctype in argtypes:
                width = ctypes.sizeof(ctype) * 8
                bounds = [0, 1, 2, (1 << (width - 1)) - 1, 1 << (width - 1), (1 << width) - 1]
                values.append(rng.choice(bounds) if rng.randrange(2) else rng.getrandbits(width))
            if name in ('countdown', 'local_loop'):
                values[0] %= 20
            if name == 'irreducible':
                values[1] %= 20
            if name in ('shift', 'arithmetic_shift'):
                values[1] %= 32  # Defined C shift domain only.
            if name in ('quotient', 'remainder'):
                x, y = map(lambda v: i32(v).value, values)
                if y == 0 or (x == -(1 << 31) and y == -1):
                    values[1] = 1
            if name in ('unsigned_quotient', 'unsigned_remainder') and values[1] == 0:
                values[1] = 1
            if name == 'logical':
                values = [int(bool(v)) for v in values]
            cases.append(values)
            expected.append(int(fn(*values)) & ((1 << bits) - 1))
        rows = ', '.join('[' + ', '.join(map(str, vs)) + ']' for vs in cases)
        runner.append(f'def check_{name} : IO Unit := do')
        runner.append(f'  for row in ([{rows}] : List (List Nat)) do')
        call = f'v_{name}.eval ' + ' '.join(
            f'(BitVec.ofNat {ctypes.sizeof(t) * 8} row[{i}]!)' for i, t in enumerate(argtypes))
        call += f' 1000 {choices}'
        runner += [f'    match ({call}).1 with',
                   '    | .returned value => IO.println value.toNat',
                   '    | other => throw (IO.userError (reprStr other))']
    runner += ['def main : IO Unit := do'] + [f'  check_{s[0]}' for s in specs]
    path = work / 'Runner.lean'
    path.write_text('\n'.join(runner) + '\n')
    output = run([args.lake, 'env', 'lean', '--run', path], env=env).stdout
    observed = [int(line) for line in output.splitlines() if line.strip()]
    assert observed == expected, next(((i, a, b) for i, (a, b) in enumerate(zip(observed, expected))
                                      if a != b), (len(observed), len(expected)))
    corrupted = expected.copy()
    corrupted[0] ^= 1
    assert observed != corrupted, 'native differential test failed to detect a mutation'
    print(f'PASS {len(expected)} native C/Lean comparisons, including mutation detection', flush=True)

    replay_lib = work / 'replay.so'
    run(['cc', '-shared', '-fPIC', '-O2', ROOT / 'tests/replay.c', '-o', replay_lib])
    replay = ctypes.CDLL(str(replay_lib)).replay
    replay.argtypes = [u32, u32, ctypes.POINTER(u32)]
    replay.restype = ctypes.c_int
    replay_source = ['import Constrained', 'import Bad', 'import Pruned',
                     'open GotoLean', 'def main : IO Unit := do']
    replay_expected = []
    for kind, name in enumerate(['constrained', 'bad', 'pruned']):
        for value in range(16):
            result = u32()
            status = replay(kind, value, ctypes.byref(result))
            replay_expected.append(f'{status} {result.value if status == 0 else 0}')
            call = (f'v_constrained.eval 20 [0, 0, {value}]' if kind == 0
                    else f'v_{name}.eval {value} 20')
            replay_source += [f'  match ({call}).1 with',
                              '  | .returned r => IO.println s!"0 {r.toNat}"',
                              '  | .assertionFailed _ => IO.println "1 0"',
                              '  | .assumptionRejected _ => IO.println "2 0"',
                              '  | other => throw (IO.userError (reprStr other))']
    (work / 'Replay.lean').write_text('\n'.join(replay_source) + '\n')
    replay_output = run([args.lake, 'env', 'lean', '--run', work / 'Replay.lean'], env=env).stdout
    assert replay_output.splitlines() == replay_expected
    print(f'PASS {len(replay_expected)} native source/Lean nondeterminism and check replays', flush=True)

    regressions = '\n'.join('import ' + module(n) for n in names) + '''
open GotoLean
#guard (v_bad.eval 7 20).1 matches .assertionFailed _
#guard (v_bad.eval 6 20).1 == .returned 6
#guard (v_pruned.eval 12 20).1 matches .assumptionRejected _
#guard (v_pruned.eval 9 20).1 == .returned 9
#guard v_constrained.eval 20 [42, 73, 9, 99] == (.returned 9, [99])
#guard (v_constrained.eval 20 [0, 0, 10]).1 matches .assumptionRejected _
#guard (v_constrained.eval 20 []).1 matches .choiceError _
#guard (v_constrained.eval 20 [0, 0, 4294967296]).1 matches .choiceError _
#guard (v_uninitialized.eval 20 [73]).1 == .returned 73
#guard (v_self_read.eval 20 [41]).1 == .returned 42
#guard v_read_before_write.eval 20 [41, 73, 99] == (.returned 41, [99])
#guard (v_bad_spin.eval 20).1 matches .assertionFailed _
#guard (v_countdown.eval 10 1).1 matches .exhausted _
#guard (v_countdown.eval 10 100).1 == .returned 0
#guard (v_shift.eval 4294967295 32 20).1 == .returned 0
#guard (v_shift.eval 4294967295 4294967295 20).1 == .returned 0
#guard (v_arithmetic_shift.eval 2147483648 32 20).1 == .returned 4294967295
#guard (v_quotient.eval 7 0 20 [99]).1 == .returned 99
#guard (v_remainder.eval 7 0 20 [42]).1 == .returned 42
#guard (v_quotient.eval 2147483648 4294967295 20).1 == .returned 2147483648
#guard (v_remainder.eval 2147483648 4294967295 20).1 == .returned 0
#guard (v_select_effect.eval 0 123 20).1 == .returned 99
'''
    (work / 'Regressions.lean').write_text(regressions)
    run([args.lake, 'env', 'lean', work / 'Regressions.lean'], env=env)
    run([args.lake, 'env', 'lean', ROOT / 'examples/Proofs.lean'], env=env)
    print('PASS vcgen proofs, assertion/assumption outcomes, choice replay and bounds', flush=True)

    if args.ir:
        ir_obj = work / 'ir.gb'
        answers = run([args.ir, ir_obj]).stdout.splitlines()
        ir_runner = []
        for row in answers:
            name, value = row.split('\t')
            path = work / f'Ir{module(name)}.lean'
            run([args.printer, ir_obj, '--function', name, '-o', path])
            ir_runner.append(path.read_text().replace('import GotoLean\n', ''))
            ir_runner.append(f'#guard (v_{name}.eval 10).1 == .returned ({value})\n')
        for name in ['lazy_choice', 'bool_choice', 'array_oob', 'union_padding', 'byte_extract_partial', 'byte_update_dynamic']:
            path = work / f'Ir{module(name)}.lean'
            run([args.printer, ir_obj, '--function', name, '-o', path])
            ir_runner.append(path.read_text().replace('import GotoLean\n', ''))
        ir_runner += ['#guard (v_lazy_choice.eval 10).1 == .returned 42',
                      '#guard (v_bool_choice.eval 10 [0]).1 == .returned false',
                      '#guard (v_bool_choice.eval 10 [1]).1 == .returned true',
                      '#guard (v_bool_choice.eval 10 [2]).1 matches .choiceError _',
                      '#guard (v_array_oob.eval 10 [83]).1 == .returned 83',
                      '#guard (v_array_oob.eval 10 []).1 matches .choiceError _',
                      '#guard (v_union_padding.eval 10 [0]).1 == .returned 37',
                      '#guard (v_union_padding.eval 10 [1]).1 == .returned 293',
                      '#guard (v_byte_extract_partial.eval 10 [0]).1 == .returned 18',
                      '#guard (v_byte_extract_partial.eval 10 [65280]).1 == .returned 65298',
                      '#guard (v_byte_update_dynamic.eval 10 [3]).1 == .returned 3442759288',
                      '#guard (v_byte_update_dynamic.eval 10 [4294967295]).1 == .returned 305419896']
        (work / 'IrOracle.lean').write_text('import GotoLean\n' + '\n'.join(ir_runner))
        run([args.lake, 'env', 'lean', work / 'IrOracle.lean'], env=env)
        print(f'PASS {len(answers)} CBMC IR oracle cases, Boolean choices and lazy evaluation', flush=True)

    bad_obj = work / 'unsupported.gb'
    run([args.goto_cc, '-c', ROOT / 'tests/unsupported.c', '-o', bad_obj])
    preserved = work / 'preserved.lean'
    for name in ['floating', 'calls', 'indirect', 'missing',
                 'parameter_address']:
        preserved.write_text('keep me\n')
        result = run([args.printer, bad_obj, '--function', name, '-o', preserved], ok=False)
        assert result.returncode == 2 and name in result.stderr, result
        assert preserved.read_text() == 'keep me\n'
        if name == 'parameter_address':
            assert 'address-taking of parameters' in result.stderr
    for name, expected in [('global_read', 0), ('global_write', 1),
                           ('global_roundtrip', 35), ('global_memory', 83),
                           ('statics', 1), ('static_roundtrip', 3)]:
        path = work / f'{module(name)}.lean'
        run([args.printer, bad_obj, '--function', name, '-o', path])
        path.write_text(path.read_text() +
                        f'\n#guard (v_{name}.eval 30 (List.replicate 20 0)).1 matches .returned ({expected}, _)\n')
        run([args.lake, 'env', 'lean', path], env=env)
    path = work / 'StructArgument.lean'
    run([args.printer, bad_obj, '--function', 'structs', '-o', path])
    path.write_text(path.read_text() + '\n#guard (v_structs.eval 8589934599 10).1 == .returned 7\n')
    run([args.lake, 'env', 'lean', path], env=env)
    malformed = work / 'malformed.gb'
    malformed.write_text('not a goto binary\n')
    result = run([args.printer, malformed, '--function', 'x', '-o', preserved], ok=False)
    assert result.returncode == 2 and preserved.read_text() == 'keep me\n'
    assert not list(work.glob('*.tmp.*'))
    print('PASS unsupported inputs, malformed binary, and output preservation', flush=True)


if __name__ == '__main__':
    main()
