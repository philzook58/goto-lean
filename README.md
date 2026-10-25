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

[Use your own C](docs/WORKFLOW.md):
`python3 tools/translate.py input.c --function process --out build/try`
generates a model and preserves a separate starter spec.
[Detailed commands and semantics](docs/REFERENCE.md).

For AI-assisted proof development, use the repository's
[`goto-lean` skill](.agents/skills/goto-lean/SKILL.md) and
[agent proof guide](docs/AGENT_GUIDE.md). The guide covers replay choices,
universal checks, loop invariants and counterexample certificates.

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

## Three examples to review

| Example                                                      | Checked guarantee                                                                        |
| ------------------------------------------------------------ | ---------------------------------------------------------------------------------------- |
| [Assertions in C](examples/checks/checks.c)                  | Five universal Lean proofs, including selected inserted safety checks                    |
| [Fill and its caller](examples/arrays/Spec/CheckedFill.lean) | Unbounded checked fill; a caller establishes its memory premises                         |
| [Bug/repair pairs](examples/violations/README.md)            | Named violations certified in Lean; repairs checked by CBMC and concrete Lean executions |

[Array contracts](examples/arrays/README.md), the [token parser](examples/parser/README.md),
[three real-code case studies](examples/case-studies/README.md), and the
[compatibility inventory](COMPATIBILITY.md) contain the remaining examples and limits.

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
example directories (except the tutorial's `Generated/Add.lean`), build outputs and local receipts are ignored; handwritten
imports, runtime, specifications and proofs stay in Git.

# AI Disclosure
Agents were heavily used to make this project
