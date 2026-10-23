# A small local verification receipt

In `examples/checks`, `examples/arrays`, or `examples/violations`:

```sh
make check       # regenerate, prove, audit named claims, write the receipt
make status      # reject a receipt whose current inputs/artifacts no longer match
```

The shared runner is `tools/verification.py`, using only Python's standard library.
Each example's short `verification.json` is reviewed policy: compilation/check
flags, entries and reachable callee coverage, expected property counts by function
and category, proof modules, named claims and scope labels. It does not discover
what the user intended to verify.

## What is bound

`.lake/verification/` contains:

| File | Meaning |
| --- | --- |
| `input.i` | Captured preprocessed C, used as the frontend's compilation input |
| `raw.gb`, `checked.gb` | GOTO before and after the selected instrumentation |
| `properties.json` | Actual CBMC property IDs, categories, predicates and source locations |
| `generated.json` | Generation inputs/tool identities, artifact hashes and entry/property mapping; not proof success |
| `Audit.lean`, compiled proof modules | The checked claims and transitive axiom checks |
| `result.json` | Local receipt issued only after proof checking and revalidation |

The receipt records source/header hashes from preprocessing, configuration,
preprocessed-input hash, tool versions/binary hashes, GOTO/generated Lean hashes,
proof/model/package inputs and compiled local Lean artifacts. The actual property
inventory must match the reviewed category counts. Each emitted entry must retain
the properties of its declared function/callee scope. Missing assertions or a
disabled safety flag therefore cannot silently reduce this expected coverage.

`generate` clears an older receipt and compiles the captured input; `check`
validates that generation, builds/checks the proof modules, resolves/audits the
named declarations and rechecks inputs before writing `result.json`. Failure
leaves no new successful receipt. Proof edits can be checked without retranslating
unchanged C:

```sh
python3 ../../tools/verification.py check
```

`status` recomputes fingerprints and the GOTO property inventory; it does not
rerun the proofs. Any mismatch makes it exit unsuccessfully. Run generation again
for changed C/configuration/artifacts, or check again for changed proofs/models.
For simplicity, the dependency set includes all local example Lean and all
project runtime/proof-library sources and local compiled caches. An unrelated
edit/build can conservatively invalidate a receipt. Reuse the same tool selections
(`GOTO_CC`, `GOTO_INSTRUMENT`, `GOTO_LEAN`); paths/configuration are part of this
local identity. Use one generation/check writer per example at a time.

## Scope and limits

Scopes are explicit: `unbounded`, `execution`, or `counterexample`. Checked fill
has unbounded safety/completion claims; the other six checked array entries have
concrete execution claims. **Scope labels come from policy, not inference from
the theorem's type.** Named declarations are actually compiled, resolved and
axiom-audited, but reviewing whether their statements justify the label and
entry association remains necessary.

This receipt covers the selected **Lean claims**. It excludes native comparisons,
concrete replay commands and CBMC comparison results. In checks/violations,
`make cbmc` checks Lean first, then runs CBMC separately. Array `checked-cbmc`
checks separate bounded C harnesses; its evidence is not this receipt.

Counts and ID presence are coverage checks, not a proof of predicate meaning.
The full predicates and all source hashes are recorded, but semantic changes,
weak assumptions or a changed claim still require review. Source labels and the
printer remain trusted; this is not translation validation or a proof that the
expected inventory is complete for all C safety obligations.

The receipt is editable local build data, not a signed attestation, portable proof
certificate, or a defense against a dishonest runner/toolchain. A copied JSON file
without successful current revalidation is not evidence of the current workspace.
See [the confidence review](CONFIDENCE.md) for remaining semantic trust boundaries.

`tests/verification.py` exercises positive issuance and rejection of stale
source/headers/configuration/entry/ABI, changed tools/artifacts/proofs, missing
assertions, disabled instrumentation and nonexistent claims. It is part of CTest.
