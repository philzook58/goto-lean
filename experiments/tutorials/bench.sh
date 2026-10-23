#!/usr/bin/env bash
# Run from the project root, after run.py. Optional argument: matching CBMC binary.
set -euo pipefail
cbmc=${1:-build/bin/cbmc}

# An insufficient bound must fail only the unwinding assertion, not a lock assertion.
status=0
"$cbmc" build/tutorials/examples.gb --function lock_fixed --no-standard-checks \
  --unwind 16 --unwinding-assertions > build/tutorials/unwind.log || status=$?
test "$status" = 10
failures=$(rg 'FAILURE' build/tutorials/unwind.log)
test -n "$failures"
if printf '%s\n' "$failures" | rg -v '\.unwind\.'; then exit 1; fi

# Bound the input so unwinding assertions establish complete bounded checks.
for bound in 32 128 512; do
  echo "CBMC: times <= $bound (12 second timeout)"
  status=0
  time timeout 12 "$cbmc" experiments/tutorials/examples.c --function lock_fixed \
    --no-standard-checks "-DLOCK_BOUND=$bound" --unwind "$((bound + 1))" \
    --unwinding-assertions > "build/tutorials/lock-$bound.log" || status=$?
  test "$status" = 0 || test "$status" = 124
  echo "exit $status (0 = proved, 124 = timeout)"
done

# Check all iteration counts using the manual invariant (also checks two small proofs).
echo 'Lean: all 32-bit iteration counts'
time env LEAN_PATH=build/tutorials lake env lean experiments/tutorials/Annotated.lean
