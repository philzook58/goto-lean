GOTO_CC ?= ../../build/bin/goto-cc
GOTO_LEAN ?= ../../build/bin/goto-lean
GOTO_INSTRUMENT ?= ../../build/bin/goto-instrument
CBMC ?= cbmc
OBJECT_BITS = $(shell python3 -c 'import json; print(json.load(open("verification.json")).get("object_bits", 8))')

.PHONY: generate check status cbmc probe-pointer
export GOTO_CC GOTO_LEAN GOTO_INSTRUMENT

generate:
	python3 ../../tools/verification.py generate

check: generate
	python3 ../../tools/verification.py check
	lake env lean Audit.lean
	lake env lean Replay.lean
	python3 compare.py

status:
	python3 ../../tools/verification.py status

# Disable analysis-time defaults: both tools must see the same already-inserted checks.
cbmc: check
	$(CBMC) --object-bits $(OBJECT_BITS) .lake/verification/checked.gb --function checked_abs --no-standard-checks
	$(CBMC) --object-bits $(OBJECT_BITS) .lake/verification/checked.gb --function checked_index --no-standard-checks
	$(CBMC) --object-bits $(OBJECT_BITS) .lake/verification/checked.gb --function checked_divide --no-standard-checks
	$(CBMC) --object-bits $(OBJECT_BITS) .lake/verification/checked.gb --function checked_shift --no-standard-checks
	$(CBMC) --object-bits $(OBJECT_BITS) .lake/verification/checked.gb --function checked_add --no-standard-checks

# Pointer instrumentation uses mutable CPROVER globals and exact live object sizes.
probe-pointer:
	mkdir -p .lake
	$(GOTO_CC) -std=c11 -c ../arrays/algorithms.c -o .lake/pointer-raw.gb
	$(GOTO_INSTRUMENT) --pointer-check .lake/pointer-raw.gb .lake/pointer-checked.gb
	$(GOTO_LEAN) .lake/pointer-checked.gb --function bubble_sort -o .lake/PointerBubble.lean
	lake env lean .lake/PointerBubble.lean
