# Instrumented fill: proof and small edits

The reviewable contract is [Spec/CheckedFill.lean](Spec/CheckedFill.lean), proved
by [Proofs/CheckedFill.lean](Proofs/CheckedFill.lean). The proof includes safety,
filled contents, byte framing and termination for arbitrary admitted C lengths.
The completion bound grows with the input; this is not bounded loop unwinding.

Caller preconditions are explicit:

- All array elements are readable initially (`WordsAt`).
- The byte range does not wrap the 56-bit pointer-offset field.
- When the length is nonzero, the allocation size fits the 64-bit object-size
  result and its ID differs from CPROVER's recorded freed/dead IDs (`ObjectState`).

Object identity and bounds for each store follow from the array view. The proof
establishes the imported guards, rather than assuming the six assertions. Stores
preserve object sizes and global metadata, so these facts remain true throughout
the loop. The generic loop ranking/checkpoint machinery is reused unchanged.
The existing raw fill proof and its public statement remain unchanged.

## Edit experiment

Experiments used copies under `.lake/fill-edits/`; upstream sources were not edited.
For each copy, compile with `goto-cc -std=c11 -Iupstream -c`, insert the same five
check flags as `make checked`, then translate `--function fill`. Compile it in an
isolated Lean module and use copies of the contract/proof with only imports changed.
This prevents accidentally reusing the original generated implementation.

| C edit | Unchanged proof | Repair |
| --- | --- | --- |
| Compile fill alone, changing global GOTO numbers | Pass | None |
| Prepend a comment and blank lines | Pass | None |
| Replace `++i` with `i += 1u` | Pass | None |
| Introduce `value_type saved = v; a[i] = saved;` | Fails | Local store-step lemma: record `v_saved := s.v_v`, and simplify the overwritten declaration choice with `choose, forall_const` |
| Rename loop variable `i` to `index` | Fails | Mechanical `v_i` → `v_index` in the proof |
| Replace `i < n` with buggy `i <= n` | Fails | Deliberately unrepaired: the continuing branch no longer establishes a valid index |

Both repaired positive variants type-check with the **unchanged contract and
preconditions**, with only standard axioms. They require no new invariants,
printer changes or proof framework. The off-by-one negative is also represented
by the independently checked bug/repair suite in `examples/violations/`.

These are initial observations, not a promise of general edit stability. The
proof still refers to generated locals and checkpoint/body constructors `.b2`
and `.b3`; edits that change that control flow can require repairs. It does not
refer to source line numbers, global GOTO numbers, assertion-site strings or the
exit block's number. No maintained edit-repair automation was added for this
one-off experiment.
