# goto-lean

Write properties in C. Translate CBMC's GOTO program to executable Lean.
Use Lean proofs to establish those properties beyond a chosen loop-unwinding bound.

```c
#include <limits.h>
int checked_add(int x) {
    __CPROVER_assume(x < INT_MAX);                  // caller's precondition
    int result = x + 1;
    __CPROVER_assert(result > x, "increment increases the value");
    return result;
}
```

CBMC inserts a signed-overflow assertion too. The Lean proof checks **both**
assertions for every admitted input. You can read the claim in the C and skip
the Lean proof tactics.

```text
C + assertions → instrumented GOTO → generated Lean → handwritten Lean proof
                                           ↘ concrete execution
```

Translation alone does not prove anything. Generated Lean keeps bitvector
expressions, control-flow blocks, and source/property IDs visible. Proofs and
loop invariants live in separate files. The translator is a small C++ printer;
it does not infer invariants or silently remove checks.

## Start here

[Three short, runnable tutorials](docs/TUTORIAL.md):

1. Read a C assertion, execute the Lean version, and check a universal proof.
2. See an actual CBMC violation and its kernel-checked Lean certificate.
3. Read an unbounded array contract without reading the loop proof.

[Use your own C, or give an AI the task](docs/WORKFLOW.md).
[Detailed commands and semantics](docs/REFERENCE.md).

## Build once

Requires a C/C++ toolchain (C++17), CMake 3.24+, Ninja, Bison, Flex, zlib headers, and
Lean/Lake **4.35.0**. Example runners also use Python 3 and a native C compiler.

```sh
cmake -S . -B build -G Ninja
cmake --build build --target goto-lean-tools -j4
lake build
```

CMake fetches pinned CBMC 6.11.0 source. A preinstalled CBMC executable is only
needed for the optional comparison commands; see the [reference](docs/REFERENCE.md).

## What is established today?

| Example | Checked guarantee |
| --- | --- |
| [C assertion examples](examples/checks/checks.c) | Five universal Lean proofs, including selected inserted safety checks |
| [Instrumented fill](examples/arrays/Spec/CheckedFill.lean) | Unbounded safety, filled contents, byte framing, and termination |
| [Seven array contracts](examples/arrays/Spec.lean) | Universal proofs over raw translations; six still await universal proofs of imported checks |
| [12 bug/repair pairs](examples/violations/README.md) | Named violations certified in Lean; repairs checked by CBMC and concrete Lean executions |

The generated program, its preconditions and the exact theorem determine the
claim. C translation, the C++ printer and agreement of the memory model with
CBMC remain trust boundaries. Full CBMC IR and every optional safety check are
not yet supported; unsupported reachable constructs fail explicitly.
[Coverage](COMPATIBILITY.md) records the current subset and limitations.
[Sources of false confidence](docs/CONFIDENCE.md) examines weak specifications,
vacuous assumptions, missing checks, stale artifacts and unproved model fidelity.
The same page records implemented safeguards and [next steps](docs/CONFIDENCE.md#next-steps).
The checked examples have [local Lean receipts](docs/RECEIPTS.md): `make status`
revalidates source/configuration, property inventory, generated code and proofs.

Run the regression suite with `ctest --test-dir build --output-on-failure`.
New semantics should have a successful example and a certified failing example.

[GitHub Actions](.github/workflows/ci.yml) regenerates Lean from the checked-in C
and runs the regressions serially in a container limited to 4 GiB. Generated
example directories, build outputs and local receipts are ignored; handwritten
imports, runtime, specifications and proofs stay in Git.
