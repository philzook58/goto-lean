# CBMC tutorial experiments

The useful division of work is automatic bug finding in CBMC, checked concrete
witnesses in Lean, and manual invariants when loop unwinding becomes expensive.
Lean also found three counterexamples itself, after unfolding the generated
block definitions into bitvector propositions.

Sources are Kroening, Schrammel and Tautschnig's
[CBMC chapter](https://arxiv.org/abs/2302.02384), Sections 2, 3.1 and 3.3
(CC BY 4.0), and Philip Zucker's
[CBMC tutorial](https://www.philipzucker.com/cbmc_tut/).
[examples.c](examples.c) makes scalar harness inputs parameters, inlines the
lock helpers, and replaces their global state with a local flag. It adds a
nonnegative-result assertion to the paper's absolute-value function and includes
two explicitly repaired variants. [memory.c](memory.c) retains the memory
examples apart from entry-point names. These are small adaptations, not a
reproduction of the paper's performance benchmark suite.

## Counterexamples and proofs

| Function | Concrete witness certified in Lean | CBMC |
| --- | --- | --- |
| `uninitialized` | uninitialized `x = 12345` | assertion fails |
| `abs32` | input `0x80000000` | signed negation overflows |
| `abs64` | input `0x8000000000000000` | nonnegative-result assertion fails |
| `before_assume` | input `0x80000000` | assertion fails before the assumption |
| `after_assume` | input `100` | assertion fails despite the assumption |
| `lock_bug` | `times = 98304`, acquisitions `[true, false, false]` | release assertion fails |

The witnesses match this run's CBMC traces. A second checked lock witness uses
just `times = 2` and `[false, false]`: the first failed acquisition decrements
zero to `UINT_MAX`; the second iteration attempts to release an unheld lock.
The trace need not finish the loop to demonstrate an assertion failure.
Concrete Lean replay also supplies values for each executed GOTO declaration,
including values that are immediately overwritten. For the shorter lock
witness, the full stream is `[0, 0, 0, 0, 0, 0]`: two entry declarations, then
a temporary declaration and acquisition bit on each iteration. The assertion
fails after the second acquisition bit.

The chapter's assumption-order example has an apparent off-by-one typo:
`result >= 1 && result <= 100` does not imply `result < 100`, although its
accompanying prose says the assertion passes. This is also present in the
[PDF](https://arxiv.org/pdf/2302.02384). Both tools find `100`.

[Counterexamples.lean](Counterexamples.lean) uses `by decide` to check each
concrete failing run by kernel reduction. The shared `failure_refutes` theorem
then proves both an explicit finite `Executes ... (.assertionFailed site)`
witness and the negation of the unbounded safety specification, for every
postcondition. Fuel exhaustion, rejected assumptions and missing choices do not
count as failures. All six certificates print only `propext` as an axiom
dependency; there are no sorries or native evaluation axioms.

For `abs32`, `goto-instrument --signed-overflow-check` inserts the assertion
before translation. The certificate therefore catches the C overflow check.
The `abs64` experiment deliberately uses raw fixed-width IR: negation wraps,
then the functional assertion fails. Signed-minimum negation is undefined in C;
this is not a claim about a compiled C program's behavior after that operation.

[Discover.lean](Discover.lean) tries three false universal safety statements.
Lean's `#guard_msgs` checks the expected counterexample diagnostics, so the
file itself compiles successfully. After finite block unfolding, `bv_decide`
reports `12345#32`, `9223372036854775808#64`, and `100#32`. Thus Lean does help
find bugs directly, but this experiment searches straight-line bitvector goals,
not arbitrary unbounded executions. Discovery is separate from the accepted
kernel-checked replay proofs. The tactic's default native checker would add a
compiler-trusting axiom to successful proofs; the accepted proofs here avoid it.

CBMC also proves the guarded example and the repaired range assertion safe.
[Annotated.lean](Annotated.lean) proves these from the generated blocks using
`vcgen` and simplification, alongside the repaired lock invariant.

## Loop scaling

One run on this Linux x86-64 host, using pinned CBMC 6.11.0 and Lean 4.35.0:

| Check | Scope | Wall time |
| --- | --- | ---: |
| CBMC repaired lock | `times <= 32`, sufficient unwinding assertions | 0.242 s |
| CBMC repaired lock | `times <= 128`, sufficient unwinding assertions | 3.116 s |
| CBMC repaired lock | `times <= 512` | timeout after 12.033 s |
| Lean annotated harness | all 32-bit `times`, all acquisition choices | 0.809 s |
| Lean discovery attempts | three models, combined | 0.601 s |
| Lean replay certificates | six functions, combined | 0.409 s |

The Lean harness timing includes the guarded and range proofs as well as the
lock proof. The lock invariant and proof occupy 21 nonblank code lines. At
the loop head, `got_lock = 0` and `held = 0`; after acquisition, both are zero
or both are one. `vcgen` checks preservation for each generated block. This
proves safety on every finite execution prefix and return value zero on normal
termination; it does not prove termination.

The bounded CBMC checks add a C assumption `times <= N` and unwind `N + 1`
times with unwinding assertions enabled. The Lean proof uses the source
without that bound. A separate unbounded-input CBMC run with unwind 16 fails
only its unwinding assertion, confirming incompleteness rather than a lock bug.
A timeout is inconclusive.

These are single wall-clock measurements with warm Lean imports, not averages
or a general speedup claim. Translation and compilation of nine generated
modules cost about 4 seconds separately; C++ compilation and manual proof
development are excluded. CBMC finds the small scalar bugs in 0.02–0.03 seconds
each without annotations. The Lean benefit is rechecking an invariant whose
cost does not scale with the iteration bound. Writing that invariant takes
human work, and its block cases currently depend on generated PC names.

## Aggregate examples and trust boundary

CBMC detects the tutorial's `buffer[10]` write into a ten-element buffer and
proves array-access bounds for the chapter's binary search (unwind 6 with
unwinding assertions). That is a memory-safety check, not a proof of search
correctness or sortedness.

Both now translate using packed finite-array values. The input is explicitly
instrumented with CBMC's bounds assertions. [Memory.lean](Memory.lean) proves
the buffer's failing execution by kernel reduction, then obtains reachability
and safety refutation through `failure_refutes`. It also checks two concrete
binary searches. The buffer proof prints only `propext` and `Quot.sound` as
axiom dependencies. A universal Lean proof of binary-search bounds has not
been added. These two experiments exercise packed values. Subsequent
[memory regressions](../../tests/Memory.lean) and the
[unchanged parser experiment](../parser/RESULTS.md) now exercise address-taking,
aliases, direct calls and copy effects. The
[original-paper probe](../paper/RESULTS.md) separately records which original
programs work without the scalar adaptations above.

Lean proves properties of the generated definitions. The C++ translation is
still a trust boundary, supported by the existing native-C and CBMC-IR
differential tests rather than a translation correctness theorem.

## Translation and proof boundary

The C++ printer translates explicit blocks and every declaration choice without
eliminating overwritten values, folding return blocks, or restructuring control
flow. This keeps translation and concrete replay predictable. Regression cases
check that overwritten declaration values are still consumed and that unused
replay inputs are returned intact.

A Boolean failure predicate and one shared Lean theorem connect concrete replay
to operational reachability and unbounded safety refutation. Proof files need
no hardcoded source-location strings or private interpreter unfolding.

Simplification belongs in Lean. The block proofs already handle overwritten
declaration choices using `vcgen` and ordinary `simp`, without a custom
optimization pass. When a clearer program view is useful, a handwritten Lean
summary should carry a proof of equivalence to the generated definitions.
Keep names and source comments readable, but let actual proof friction motivate
further machinery. These results do not justify a second CFG language, general
structuring pass, solver protocol or memory framework.

## Reproduce

Build the optional CBMC tools from the same fetched source:

```sh
cmake --build build --target goto-lean-tools cbmc goto-instrument -j4
python3 experiments/tutorials/run.py
bash experiments/tutorials/bench.sh
```

Run these from the project root. `run.py` generates the Lean modules, runs the
CBMC examples, checks the four Lean files, and translates the aggregate examples
with bounds assertions. Commands are printed; full output goes to `build/tutorials/run.log`.

`bench.sh` separately runs the slow lock-scaling comparison and prints wall
times. CBMC output goes to `build/tutorials/lock-32.log`, `lock-128.log`, and
`lock-512.log`; the insufficient-unwinding check uses `unwind.log`. Bounds and
the timeout are plain constants in this short script.

Both default to `build/bin/cbmc`; to reuse a matching binary elsewhere, pass
its path as the sole argument to each script. Generated files and logs stay
under the ignored build directory. These one-off experiments remain separate
from CTest; there is no configurable benchmark harness or JSON reporting layer.
