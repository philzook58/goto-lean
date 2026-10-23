# Bug/repair controls

This is a small, original regression suite, rather than a third-party benchmark.
Read `bugs.c` for the bug beside its repair. Run:

```sh
make check cbmc
```

Both tools consume `.lake/verification/checked.gb`, instrumented once with pointer, bounds,
signed overflow, division-by-zero and undefined-shift checks. CBMC analysis-time
standard checks are disabled so that its assertions are the ones Lean imports.
`Generated/*.lean` retains their original source locations and property IDs.

| Pair | Lean witness | Expected imported property |
| --- | --- | --- |
| maximum | x=0, y=1 | `bug_maximum.assertion.1` |
| add | x=INT_MAX | `bug_add.overflow.1` |
| negate | x=INT_MIN | `bug_negate.overflow.1` |
| divide_zero | x=7, divisor=0 | `bug_divide_zero.division-by-zero.1` |
| divide_overflow | x=INT_MIN | `bug_divide_overflow.overflow.1` |
| shift | x=1, distance=32 | `bug_shift.undefined-shift.1` |
| index | i=4 | `bug_index.array_bounds.1` |
| null | null local pointer | `bug_null.pointer_dereference.1` |
| one_past | two-byte array, offset 2 | `bug_one_past.pointer_dereference.2` |
| lifetime | pointer outlives its local | `bug_lifetime.pointer_dereference.1` |
| uninitialized | initial value=1 | `bug_uninitialized.assertion.1` |
| loop_bound | fifth write to four-byte array | `bug_loop_bound.array_bounds.1` |

All 12 negatives and all 12 repairs pass their expected tests in both tools.
The repairs widen arithmetic before evaluating it, guard invalid inputs, fix the
loop bound, keep accesses within object lifetime, or initialize the value. The
index/division/shift guards return zero on invalid inputs: that is an explicit
policy of these examples, not a prescribed API for other C programs.

## What Lean proves

`Certificates.lean` is handwritten. Each `_fails` theorem proves `Violates`:

1. The failure site contains the **specific original CBMC property ID**.
2. A finite execution of the translated program reaches that failed assertion.
3. The translated safety weakest precondition is false for this input.

A failure in the Lean model's extra memory checks, an unrelated property, a
rejected assumption, exhausted fuel or missing nondeterministic choice will not
satisfy the theorem. For lifetime, the witness selects CBMC's inserted assignment
to `__CPROVER_dead_object`; the failure happens at its imported dead-object check,
before the Lean model's memory load. One-past fails the imported object-size check.

Each `_fixed` theorem certifies a **returned** execution of the repair on the same
argument values, with all reached assertions passing. These positive Lean
certificates are concrete, not universal repair proofs. Their declaration choices
are explicit; uninitialized starts with 1 in both cases, then the repair writes 0.
All 24 proofs use kernel reduction and only standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); `#check_axioms` enforces this policy for each certificate.

## What CBMC checks

`cbmc.py` requires exit code 10 **and** failure of the named property for every
bug. A crash or another failed property does not count. It checks each repair
separately for all argument values, with all inserted checks and unwinding
assertions enabled (unwind bound six completes these short loops). There are no
input assumptions that hide the bad boundary inputs in the repairs.

CBMC traces and full positive logs are retained as `.lake/bug_*.log` and
`.lake/fixed_*.log`. Lean's witnesses are independently supplied; this suite does
not parse CBMC traces into Lean choice streams. Both certify the same property,
but their concrete input/choice witnesses need not be identical.

CBMC lists unreachable properties from other functions as successful in a repair
run. Those totals are not coverage counts. Every repair has its own entry run;
every bug has its own run targeting the specific failing property.

The regular CTest suite checks both positive and negative Lean certificates.
When CBMC is installed at CMake configuration time, it also registers the paired
CBMC test. This pairing should accompany new semantics/instrumentation coverage:
a successful return and a certified failure of the intended property.

`verification.json` declares the entry/callee coverage, expected property counts,
and concrete claims. `make check` writes a [local Lean receipt](../../docs/RECEIPTS.md);
`make status` rejects stale inputs or artifacts. `make cbmc` checks Lean first,
then runs its separate CBMC comparisons; those comparisons are not part of the receipt.
