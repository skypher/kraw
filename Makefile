override SOURCE_DATE_EPOCH := 1785283200
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

.PHONY: paper verify payload-check toolchain-info audit-fast replay-short replay-all replay-profile

paper:
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error krawtchouk_turan_positivity
	cd paper && bibtex krawtchouk_turan_positivity
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error krawtchouk_turan_positivity
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error krawtchouk_turan_positivity

payload-check:
	sha256sum -c certificates/PAYLOAD.sha256

verify: payload-check
	sha256sum -c certificates/MANIFEST.sha256

toolchain-info:
	sh scripts/toolchain-info.sh

audit-fast: verify toolchain-info replay-short
	g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
	/tmp/exhaustive-turan-scan 120

replay-short:
	python3 scripts/recurrence-and-small-scan.py
	python3 scripts/regime-decomposition.py
	python3 scripts/small-argument-cases.py
	python3 scripts/even-minimum-gap.py
	python3 scripts/odd-minimum-gap.py

replay-all: replay-short
	python3 scripts/finite-gap-offsets.py 14
	python3 scripts/fixed-argument-strips.py 12 14
	g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
	/tmp/exhaustive-turan-scan 1200

replay-profile:
	/usr/bin/time -v $(MAKE) replay-all
