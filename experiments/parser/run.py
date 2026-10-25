#!/usr/bin/env python3
"""Compare the local Cornell-experiment repair helper against its generated Lean program."""
import ctypes
import os
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PARSER = ROOT.parent / 'cornell-serial-assurance'
WORK = ROOT / 'build/parser'
TOOLS = ROOT / 'build/bin'
WORK.mkdir(parents=True, exist_ok=True)
ENV = dict(os.environ, LEAN_PATH=str(WORK))


def run(*args):
    r = subprocess.run(list(map(str, args)), cwd=ROOT, env=ENV,
                       text=True, capture_output=True, timeout=120)
    if r.returncode:
        raise RuntimeError(f'{args}\n{r.stdout}{r.stderr}')
    return r.stdout


run('lake', 'build', 'GotoLean', 'GotoLean.Audit', 'GotoLean.Contracts', 'GotoLean.MemoryViews', 'GotoLean.PointerLemmas')
run(TOOLS / 'goto-cc', '-c', PARSER / 'harness/check_word.c', '-o', WORK / 'word.gb')
for name, module in [('take_word', 'Generated/TakeWord'), ('main', 'WordMain')]:
    file = WORK / f'{module}.lean'
    file.parent.mkdir(parents=True, exist_ok=True)
    run(TOOLS / 'goto-lean', WORK / 'word.gb', '--function', name, '-o', file)
    run('lake', 'env', 'lean', '--root', WORK, '-o', file.with_suffix('.olean'), file)
run('cc', '-shared', '-fPIC', '-O2', '-I', PARSER / 'generated',
    'experiments/parser/native.c', '-o', WORK / 'native.so')
native = ctypes.CDLL(str(WORK / 'native.so')).parse_probe
native.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t,
                   ctypes.POINTER(ctypes.c_size_t)]
native.restype = ctypes.c_int
rng = random.Random(0x70CE)
rows = [(s, cap) for s in [b'', b' ', b'  hi there', b'abcdef', b'a\tb ',
                         b'ab\x00cd', b'\xff\x80 x'] for cap in [0, 1, 3, 7, 16]]
rows += [(bytes(rng.choice(b'abcde     ') for _ in range(rng.randrange(30))),
          rng.randrange(17)) for _ in range(160)]
runner = ['import Generated.TakeWord', 'open GotoLean']
expected = []
for i, (raw, capacity) in enumerate(rows):
    input = ctypes.create_string_buffer(raw)
    output = ctypes.create_string_buffer(bytes([165] * 16), 16)
    offset = ctypes.c_size_t()
    ok = native(input, output, capacity, ctypes.byref(offset))
    assert input.raw == raw + b'\0', 'native helper changed input'
    expected.append(','.join(map(str, [ok, offset.value, *output.raw])))
    source = ', '.join(map(str, [*raw, 0]))
    runner += [f'def check_{i} : IO Unit := do',
               f'  let input : Array (BitVec 8) := #[{source}]',
               '  let m : Memory := { objects := #[none, none, some input,',
               '    some (Array.replicate 16 165), some (Memory.unpack',
               '      (Pointer.make 56 2 0 : BitVec 64))] }',
               f'  match (v_take_word.eval (Pointer.make 56 4 0) (Pointer.make 56 3 0)',
               f'    {capacity} 500 [0, 0, 0] m).1 with',
               '  | .returned (value, m) =>',
               '    if m.bytes 2 != some input then throw (IO.userError "input changed")',
               '    let cursor := Memory.readBits ((m.bytes 4).getD #[]) 0 64',
               '    let bytes := ((m.bytes 3).getD #[]).toList.map BitVec.toNat',
               '    IO.println (String.intercalate ","',
               '      ((value.toNat :: Pointer.offset 56 cursor :: bytes).map toString))',
               '  | other => throw (IO.userError (reprStr other))']
runner += ['def main : IO Unit := do'] + [f'  check_{i}' for i in range(len(rows))]
(WORK / 'Native.lean').write_text('\n'.join(runner) + '\n')
observed = run('lake', 'env', 'lean', '--run', WORK / 'Native.lean').splitlines()
assert observed == expected, 'parser result, cursor or output bytes disagree'
print(f'PASS {len(rows)} unchanged take_word native C/Lean comparisons', flush=True)
print(run('lake', 'env', 'lean', 'experiments/parser/Proofs.lean').strip(), flush=True)
for module in ['Scan', 'CopyWord', 'TakeWord']:
    source = ROOT / f'examples/parser/Proofs/{module}.lean'
    output = WORK / f'Proofs/{module}.olean'
    output.parent.mkdir(parents=True, exist_ok=True)
    run('lake', 'env', 'lean', '--root', ROOT / 'examples/parser', '-o', output, source)
print(run('lake', 'env', 'lean', ROOT / 'examples/parser/Audit.lean').strip(), flush=True)
