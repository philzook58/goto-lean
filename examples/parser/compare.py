#!/usr/bin/env python3
"""Compare the twenty certified parser inputs with native C, including complete output bytes."""
import ctypes
import os
from pathlib import Path
import subprocess

Path('.lake/native-cases.c').write_text('''
#define main source_main
#include "../take_word.c"
#undef main
int run_case(const char *text, size_t capacity, unsigned char *out, size_t *advance) {
    char *cursor = (char *)text;
    int result = take_word(&cursor, (char *)out, capacity);
    *advance = (size_t)(cursor - text);
    return result;
}
''')
subprocess.run([os.environ.get('CC', 'cc'), '-std=c11', '-shared', '-fPIC',
                '-Wall', '-Wextra', '-Werror', '.lake/native-cases.c', '-o', '.lake/cases.so'], check=True)
native = ctypes.CDLL(str(Path('.lake/cases.so').resolve())).run_case
native.argtypes = [ctypes.c_char_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.POINTER(ctypes.c_size_t)]
native.restype = ctypes.c_int
rows = subprocess.run(['lake', 'env', 'lean', '-j1', '-M1024', '--run', 'Cases.lean'],
                      text=True, capture_output=True, timeout=120)
if rows.returncode:
    raise SystemExit(rows.stdout + rows.stderr)
count = 0
for row in rows.stdout.splitlines():
    if '|' not in row:
        continue
    name, data, capacity, result, advance, expected = row.split('|')
    data = bytes(map(int, data.split(',')))
    source = ctypes.create_string_buffer(data, len(data))
    output = (ctypes.c_ubyte * int(capacity))(*([165] * int(capacity)))
    cursor = ctypes.c_size_t()
    actual = native(source, int(capacity), output, ctypes.byref(cursor))
    expected = bytes(map(int, expected.split(','))) if expected else b''
    assert (actual, cursor.value, bytes(output), source.raw) == (
        int(result), int(advance), expected, data), name
    count += 1
assert count == 20, count
print('20 certified parser inputs: native C = Lean; results, cursor, input and output bytes')
