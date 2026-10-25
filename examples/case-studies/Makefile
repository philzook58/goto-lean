.PHONY: check cbmc fuzz
check:
	python3 check.py
cbmc: check
	python3 cbmc.py
fuzz:
	mkdir -p .lake/check/fuzz-corpus
	clang -std=c11 -g -O1 -fsanitize=fuzzer,address,undefined -fno-sanitize-recover=all \
	  fuzz.c json.c slide.c lookup.c -o .lake/check/fuzz
	.lake/check/fuzz .lake/check/fuzz-corpus -runs=5000 -seed=2048 -max_len=10 \
	  -rss_limit_mb=512 -timeout=10 -artifact_prefix=.lake/check/
