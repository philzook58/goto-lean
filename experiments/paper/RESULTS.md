# Coverage of the CBMC chapter

The small sequential examples are usable now. The original programs that depend
on globals, stdio, threads or floating point still expose substantial gaps.
There is no useful single percentage that describes both those examples and
the chapter's large SV-COMP performance suite.

Source: Kroening, Schrammel and Tautschnig,
[CBMC: The C Bounded Model Checker](https://arxiv.org/html/2302.02384v1),
CC BY 4.0. The local fixtures retain program behavior; headers, missing external
declarations, whitespace and PDF quote characters are normalized. The three
assumption variants are selected by preprocessing. Binary search reuses the
same function already transcribed in `../tutorials/memory.c`. These probes do
not replace global state with locals or inline helper functions in C.

| Paper example | Current result | What has actually been checked |
| --- | --- | --- |
| `abs`, Listing 1 | Translates | Imported overflow assertion fails on signed minimum; kernel-checked Lean witness; CBMC agrees |
| `binsearch`, Listing 5 | Translates | CBMC proves bounds with unwind 6 and unwinding assertions; Lean concrete replay works; a universal Lean bounds proof is still missing |
| Three `one_to_hundred` variants, §3.3 | Translate | Both assertion variants have counterexamples; the post-assumption variant still permits 100, despite the paper's prose |
| Array/assumption caveat, §3.3 | Translates | Kernel-checked failure with `a[0]=0`, `a[1]=-1`, `x=0`, `y=1`; CBMC also finds a failure |
| Original `lock`, §3.1 | Blocked at `LOCK` | Needs shared globals and initialization; direct helper calls now work in other programs |
| `login`, Listing 7 | Blocked at string-literal address | Needs addressable static strings and `printf`/`getchar` models; its finite buffers/control flow are already supported |
| `account`, §3.4 | Blocked at global `mutex` | Also needs pthread models, scheduling and synchronization; ordinary direct calls are insufficient |
| PID controller, §3.5 | Unsupported | Requires IEEE float operations, globals and input/output reporting. The printed excerpt omits its initial declarations, so it is not run as a fabricated complete program |
| Bounded `for`/`break` example, §5.3 | Blocked at external `f()` | Loop/control-flow constructs work; an explicit nondeterministic model or body for `f` is needed |

The plain range function has an assumption and no assertion. CBMC's successful
verdict for that variant is vacuous; it is not a new proof of a source assertion.
The existing tutorial experiments separately contain an annotated proof of a
range postcondition and a repaired lock adaptation. Those results do not count
as support for the original global-state lock program.

`check.py` generates six Lean modules for the supported variants and runs CBMC
on the same GOTO objects, including explicit bounds/overflow instrumentation.
It checks the four unsupported inputs fail with the expected concrete blocker.
`Proofs.lean` and `After.lean` contain kernel-checked failure certificates; there
are no sorries or native-checker axioms. Generated modules for the assumption
variants deliberately live in separate proof imports because their original
function names are identical.

```sh
python3 experiments/paper/check.py
```

An optional single argument selects a matching CBMC binary. Full results and
counterexample traces are in `build/paper/*.log`. This is a small coverage probe,
not the chapter's benchmark-suite reproduction.

The next high-value implementation is shared globals with explicit
initialization: it would remove the original lock program's current blocker and
help the command parser. Static string objects and stdio models would target
login next. IEEE floats and concurrent execution each need a larger semantic
extension. Separately, universal binary-search and `take_word` proofs require
invariants and usable function-contract rules; successful concrete execution is
not that proof.
