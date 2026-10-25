GOTO_CC ?= ../../build/bin/goto-cc
GOTO_LEAN ?= ../../build/bin/goto-lean

.PHONY: generate check
generate:
	mkdir -p .lake Generated
	$(GOTO_CC) -c take_word.c -o .lake/take_word.gb
	$(GOTO_LEAN) .lake/take_word.gb --function take_word -o Generated/TakeWord.lean

check: generate
	lake build
	lake env lean Audit.lean
	python3 compare.py
	lake env lean --run Run.lean
