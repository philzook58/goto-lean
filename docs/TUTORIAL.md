# Three short tutorials

Build once using [the README](../README.md#build-once). Commands below start at the
repository root. You do not need to read the proof tactics to follow these demos.
A green demo is a scoped claim about a model; [read what it can leave wrong](CONFIDENCE.md).

## 1. A property written in C

Read [`checked_add` in checks.c](../examples/checks/checks.c): the caller supplies
`x < INT_MAX`; the function must return a larger value. The instrumenter also
requires that signed addition does not overflow.

```sh
make -C examples/checks check
(cd examples/checks && lake env lean Replay.lean)
```

The three replays show:

- `returned 0x0000002a#32`: input 41 returned 42 as a 32-bit value.
- `assumptionRejected`: INT_MAX violates the C precondition. It is excluded.
- `exhausted`: an execution budget of zero cannot run the function.

Those are concrete runs. The universal guarantee is the header of
[`CheckExamples.addition` in Proofs.lean](../examples/checks/Proofs.lean):

```lean
theorem addition (x : BitVec 32) :
    finishes v_checked_add.step 1 (v_checked_add.initial x) (fun _ ↦ True) := by
```

Read it as: **for every admitted 32-bit input, all checks pass and execution
finishes within one block**. `True` adds no extra postcondition: the actual
functional assertion is already a check in the C program. Everything after
`by` explains why Lean accepts that statement; you can skip it initially.
False assumptions discard paths, so review the assumptions as part of the claim.

Now open [Generated/Add.lean](../examples/checks/Generated/Add.lean). Search for
`checked_add.overflow.1` and `checked_add.assertion.1`: these are the two checks
proved above. Above each operation is its original C location.

| Lean you will see | Meaning |
| --- | --- |
| `BitVec 32` | A 32-bit pattern; signed operations interpret it as signed |
| `BitVec.slt x y` | Signed `x < y` |
| `s := { s with v_result := ... }` | Update the local `result` |
| `assume site condition` | Restrict admitted executions |
| `check site condition` | An obligation the proof must establish |
| `choose site 32` | Declaration/nondeterministic bits, supplied explicitly in replay |

Generated declarations retain choices even when immediately overwritten; `[0]`
in the replay supplies one such choice. This is why its source and proof remain
literal rather than relying on a C++ simplification pass.

Optional comparison, with CBMC installed: `make -C examples/checks cbmc`.
Both tools see the same instrumented binary. This straight-line demo is easy for
both; it demonstrates the workflow, not a performance advantage.

## 2. A real failed check

Read the adjacent `bug_add` and `fixed_add` in
[bugs.c](../examples/violations/bugs.c). The bug adds in signed 32-bit arithmetic;
the repair widens to 64 bits **before** adding.

```sh
make -C examples/violations check
(cd examples/violations && lake env lean Replay.lean)
# Optional: independently find the violations and check every repair with CBMC.
make -C examples/violations cbmc
```

At INT_MAX, the bug reports `assertionFailed` at `bug_add.overflow.1`; the repair
returns `0x0000000080000000#64`, or 2147483648.

Read the header of `add_fails` in [Certificates.lean](../examples/violations/Certificates.lean).
It names that exact property and input. The theorem certifies a reachable failed
assertion and refutes the safety claim. This is stronger than printing a failing
`#eval`. `add_fixed` certifies a successful repaired execution on the same argument.
CBMC separately checks the repair for all inputs. The [suite](../examples/violations/README.md)
contains 12 such positive/negative pairs; raw logs and traces are in its `.lake/`.

## 3. An unbounded loop, with a readable contract

```sh
make -C examples/arrays check checked
```

Read [upstream/fill.c](../examples/arrays/upstream/fill.c), then the 31-line
[Spec/CheckedFill.lean](../examples/arrays/Spec/CheckedFill.lean). Its contract says:

> Given a readable array whose byte range does not wrap, with representable
> allocation size and consistent freed/dead metadata, fill completes safely,
> makes every element equal the requested value, and preserves surrounding bytes.

The metadata condition is only needed for nonempty arrays. The proof also covers
zero length with a null pointer. These are explicit caller obligations, not
assumptions silently added to the program.

`CheckedFill.implements` in [the separate proof](../examples/arrays/Proofs/CheckedFill.lean)
connects the generated program to that contract. `CheckedFill.safe` establishes
unbounded safety of the actual instrumented entry point, including all six
imported pointer checks. The completion bound grows as `2*(length+2)` blocks;
there is no chosen loop-unwinding limit. The loop invariant and ranking argument
are manual Lean annotations.

Try an edit next. [FILL_EDITS.md](../examples/arrays/FILL_EDITS.md) records which
small edits preserved the proof, which needed local repairs, and which introduced
a rejected bug. The other six instrumented array algorithms still need universal
proofs; their existing raw-translation proofs do not establish the added checks.
