# Lessons from verified-cartpole

2026-10-24. Reviewed the local sibling project `../../../verified-cartpole`: its C controller, harness, generated model, integer specification, compositional proof, mutation runner, and findings. This review did not modify cartpole sources or run external models. Temporary Lean review files were removed.

## Verified observations

- A fresh copy of `spec/Proof.lean` with the main theorem's axiom audit failed at the fixed 1,024 MB limit (exit 134, interpreter memory exception). Fresh compilation and compilation plus audit succeeded with 2,048 MB in 8.68 s and 9.13 s respectively. These are individual observations, not a repeated benchmark. The ordinary checker subsequently accepted the unchanged source and `CartpoleProof.ctrl_correct` at 2,048 MB.
- `ctrl_correct` publicly states `run.wp`, although its docstring promises completion and its proof internally establishes a bound. A temporary refactoring exposing `finishes step 20 initial Q` passed compilation and the axiom audit, using the existing proof body. The public example was initially left unchanged; the follow-up below now exports that result.
- The project's reported whole-function/long-segment slowdown is documented in its `FINDINGS.md`; this review did not rerun the multi-minute examples. Existing `leadsTo`, `finishes_of_leadsTo`, `Action.wp_ite`, and `finishes_resume` already address that problem. They should be developed and benchmarked further rather than replaced with more whole-function unfolding.
- Native compilations reproduced three functional witnesses: gain sign, input `(37,-9,38,0)`, original −789 versus mutant 1107; wrap boundary, `(1200,0,1200,0)`, 2047 versus −2047; arithmetic shift replaced with truncating division, `(0,-1,0,0)`, −133 versus −132. This review did not rerun CBMC. Native witnesses are concrete evidence, not universal proofs or kernel-checked replay certificates.

## Small tool improvement made

The skill's `check_spec.py` now accepts `--memory-mb`, retaining its 1,024 MB default. Both compilation and audit use the chosen allowance. The guide documents the option and distinguishes a resource failure from a program counterexample.

Validated against the actual cartpole proof at 2,048 MB. An unsupported-axiom fixture and a weakened-postcondition adapter still failed; a nonpositive memory value was rejected. Increasing the resource allowance does not loosen the statement or axiom checks. The frozen controlled-study evidence retains the earlier checker version.

## Small follow-up implemented

Added only `ReturnPost` to the existing `GotoLean.CallSummary` module. Cartpole uses its typed witness to remove all three impossible-return case splits. The original postconditions were proved equivalent to their prior definitions, and the existing `ctrl_correct` signature is unchanged. A new `ctrl_completes` exports the existing 20-block guarantee; `ctrl_correct` is its WP corollary. The proof is 192 lines versus 196 before, including the new public theorem. The new and existing public claims passed the axiom audit at 2,048 MB. No printer changes, arithmetic tactic, or generated wrapper framework were added.

## Proposed next library/tool changes, in order

1. **Make bounded composition easier to use.** Generate typed return-postcondition helpers for each function, including an explicit memory relation when needed. Cartpole hand-writes `RetWrap`/`RetStep` and repeatedly unpacks the global `Value` sum. Build convenience rules over the existing proved `finishes_resume` and segment API to hide stack plumbing and fuel subtraction. Require helpers to be derived from the semantics, not assumed contracts. A useful acceptance test is a smaller cartpole proof with the same input assumptions, result, and completion guarantee.
2. **Provide signed-arithmetic normalization and stable check goals.** Cartpole's `int_close` repeats bounded-modulus elimination before `omega`; accumulation proofs separately unfold overflow checks, sign extension and shifts. A small named simp set/tactic could normalize these with proved range side conditions. Preserve the distinction between C truncating division/remainder and floor division/arithmetic shifts. Label verification conditions with existing property IDs instead of making users depend on `case refine_9` and `refine_10`, which shift when instrumentation changes. Do not claim a generic `omega` solution for nonlinear variable multiplication.
3. **Export and check the requested public claim.** Offer a direct named completion theorem and derive its WP corollary. Accept explicit requirements in verification records: public theorem, input assumptions, result, instrumented checks, and model/source hashes. Keep controller correctness, ideal linear stability, and quantized disturbed balance as separate claims: `Balance.balances` still contains `sorry`, while `Ideal.stable` concerns a different, idealized loop. A successful project build does not close that gap.
4. **Make mutation outcomes diagnostic.** The existing script swaps the shared model and maps every nonzero proof-build exit to `REJECT`, suppressing diagnostics. Use isolated mutation projects and separate translation errors, proof errors, resource limits, and witnessed semantic mismatches. Retain the three concrete witnesses and eventually certify them through the replay API. A changed CFG can break a positional proof even without establishing a counterexample.

Exact rational certificate checking for plant stability is also useful, but belongs in a separate mathematical certificate library. It is lower priority for goto-lean than bounded composition and integer arithmetic: floating solver output must remain untrusted, and these plant results must not be presented as C controller guarantees.
