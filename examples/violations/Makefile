GOTO_CC ?= ../../build/bin/goto-cc
GOTO_LEAN ?= ../../build/bin/goto-lean
GOTO_INSTRUMENT ?= ../../build/bin/goto-instrument
CBMC ?= cbmc
export GOTO_CC GOTO_LEAN GOTO_INSTRUMENT

.PHONY: generate check status cbmc
generate:
	python3 ../../tools/verification.py generate

check: generate
	python3 ../../tools/verification.py check
	lake env lean Replay.lean

status:
	python3 ../../tools/verification.py status

cbmc: check
	CBMC=$(CBMC) python3 cbmc.py
