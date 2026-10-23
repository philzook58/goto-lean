# Specifications in C, checked in Lean and CBMC

Start with [`checks.c`](checks.c). Its `__CPROVER_assume` statements are the
visible preconditions; its `__CPROVER_assert` statements are the guarantees.
Both tools check the same instrumented GOTO binary.

| Function | Source assertion | CBMC-inserted obligations |
|---|---|---|
| `checked_abs` | Absolute value is nonnegative | Signed negation does not overflow |
| `checked_index` | Selected prime is positive | Index is below the four-element array bound |
| `checked_divide` | Division by one returns the input | Nonzero divisor; signed division does not overflow |
| `checked_shift` | Shift by zero returns the input | Shift distance is below the bit width |
| `checked_add` | Increment increases the signed value | Signed addition does not overflow |

There are five source assertions and six inserted properties. `make generate`
writes the exact predicates and source/property IDs to `.lake/verification/properties.json`.
Generated Lean `check` operations retain those IDs. `verification.json` declares
the expected property counts and named claims. `make check` regenerates the
artifacts, checks the inventory, then checks the Lean proofs and their axioms.
`make status` revalidates the [local receipt](../../docs/RECEIPTS.md). No C++ source-level rewriting or proof-specific folding
is involved.

## What the Lean theorems mean

[`Proofs.lean`](Proofs.lean) proves completion of each generated entry for every
input satisfying the assumptions written in C. Its final postcondition is
`True`: the functional assertions are already executable checks inside the
program, so there is no second functional specification to keep synchronized.
The definition of `finishes` requires every feasible `check` to succeed; an
assertion is never treated as an assumption.

A false assumption discards its path. Thus `checked_abs(INT_MIN)` is excluded,
not proved to return a valid result. The assumed domain is nonempty for every
example. No source assumption is inferred from a desired assertion.
These functions are straight-line programs, so CBMC also proves their complete
input domains without loop annotations. This is a coverage demonstration, not
a benchmark claiming an advantage over CBMC.

The proofs use only standard Lean axioms. The C/GOTO translation, the C++ printer
and semantic agreement of the runtime model remain trust boundaries. Native
addition/subtraction/multiplication overflow predicates are additionally tested
against 144 constant-expression answers from pinned CBMC across signed and
unsigned widths 8, 32, 64 and 128.

## Run

From the project root, first build the printer, frontend and instrumenter:

```sh
cmake --build build --target goto-lean-tools goto-instrument -j2
cd examples/checks
make check
make cbmc
```

`make cbmc` requires CBMC on PATH. It disables analysis-time standard checks
because the selected checks have already been inserted by `goto-instrument`.
This matters: checks added privately inside a separate CBMC run would not be
present in the file translated to Lean. Each function is checked as an entry;
properties unreachable from one entry are not counted as evidence about another.

## What this does not cover

This is not full support for every CBMC safety instrumenter. In particular:

- `make probe-pointer` now translates and type-checks pointer-instrumented bubble
  sort. CPROVER state is stored as mutable globals, with live object-size queries.
  The [array safety runs](../arrays/SAFETY.md) cover all seven algorithms. Global
  address-taking, heap allocation and exact dead-object sizes remain unsupported.
- `--bounds-check` alone adds no array-index property to that pointer-based
  bubble-sort body. It requires pointer instrumentation. Packed finite-array
  indexing, as in `checked_index`, is a different case.
- The existing pointer-array proofs establish the Lean model's allocation,
  lifetime and whole-object bounds checks. They are not proofs of CBMC's complete
  pointer, subobject, alignment or effective-type checks.
- The new arithmetic mapping covers `overflow-+`, `overflow--` and `overflow-*`.
  Other instrumentation expressions, including `overflow-shl`, remain subject
  to the translator's explicit subset checks. Floating-point checks are unsupported.

The larger array examples prove their `Spec.lean` contracts over raw algorithm
translations. Instrumented fill additionally has an unbounded proof covering
its six imported pointer checks; see [its contract](../arrays/Spec/CheckedFill.lean).
Their C assertion harnesses in `examples/arrays/` are
bounded CBMC checks; those harnesses have not yet been universally verified in
Lean. Likewise, quantified CPROVER assertions and CPROVER function-contract
features are not claimed supported by these five examples.
