GOTO_CC ?= ../../build/bin/goto-cc
GOTO_INSTRUMENT ?= ../../build/bin/goto-instrument
CBMC ?= cbmc
GOTO_LEAN ?= ../../build/bin/goto-lean
CC ?= cc
export GOTO_CC GOTO_LEAN GOTO_INSTRUMENT

.PHONY: generate generate-checked check cbmc benchmark-scale checked checked-cbmc status
generate:
	mkdir -p .lake Generated
	$(GOTO_CC) -std=c11 -c algorithms.c -o .lake/algorithms.gb
	$(GOTO_LEAN) .lake/algorithms.gb --function lower_bound -o Generated/LowerBound.lean
	$(GOTO_LEAN) .lake/algorithms.gb --function fill -o Generated/Fill.lean
	$(GOTO_LEAN) .lake/algorithms.gb --function find -o Generated/Find.lean
	$(GOTO_LEAN) .lake/algorithms.gb --function is_sorted_until -o Generated/IsSortedUntil.lean
	$(GOTO_LEAN) .lake/algorithms.gb --function rotate -o Generated/Rotate.lean
	$(GOTO_LEAN) .lake/algorithms.gb --function bubble_sort -o Generated/BubbleSort.lean
	python3 prepare.py
	$(GOTO_CC) -std=c11 -Iupstream -c bug.c -o .lake/bug.gb
	$(GOTO_LEAN) .lake/bug.gb --function lower_bound_bug -o Generated/Bug.lean

check: generate-checked
	lake build
	lake env lean Audit.lean
	lake env lean ../../tests/Paths.lean
	python3 ../../tools/verification.py check
	$(CC) -std=c11 -Wall -Wextra -Werror replay.c -o .lake/replay
	python3 compare.py
	$(CC) -std=c11 -Wall -Wextra -Werror scale.c -o .lake/scale
	python3 scale.py

cbmc: generate
	python3 cbmc.py

benchmark-scale: generate
	lake build
	python3 benchmark_scale.py

# Translate the instrumented algorithms; replay rejects any failed check.
generate-checked: generate
	python3 ../../tools/verification.py generate

checked: generate-checked
	python3 ../../tools/verification.py check
	lake env lean CheckedExecutions.lean
	sed 's/^import Generated$$/import Checked/' Replay.lean > .lake/CheckedReplay.lean
	sed 's/^import Generated$$/import Checked/' Scale.lean > .lake/CheckedScale.lean
	$(CC) -std=c11 -Wall -Wextra -Werror replay.c -o .lake/replay
	python3 compare.py .lake/CheckedReplay.lean
	$(CC) -std=c11 -Wall -Wextra -Werror scale.c -o .lake/scale
	python3 scale.py .lake/CheckedScale.lean

# All nondeterministic inputs, with arrays bounded to four elements.
checked-cbmc:
	python3 safety.py

status:
	python3 ../../tools/verification.py status
