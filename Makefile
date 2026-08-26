override SOURCE_DATE_EPOCH := 1787702400
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

.PHONY: paper verify payload-check toolchain-info audit-fast replay-short replay-all replay-profile pdf-preflight export-independent-witnesses independent-check independent-scan mutation-test audit-independent

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

audit-fast: verify toolchain-info replay-short independent-check mutation-test
	g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
	/tmp/exhaustive-turan-scan 120
	g++ -std=c++17 -O2 -fopenmp -Wall -Wextra -Werror -pedantic -o /tmp/independent-pascal-scan cpp/independent-pascal-scan.cpp
	/tmp/independent-pascal-scan 120

replay-short:
	python3 -u scripts/recurrence-and-small-scan.py
	python3 -u scripts/regime-decomposition.py
	python3 -u scripts/small-argument-cases.py
	python3 -u scripts/even-minimum-gap.py
	python3 -u scripts/odd-minimum-gap.py

replay-all: replay-short
	$(MAKE) export-independent-witnesses
	g++ -O2 -fopenmp -o /tmp/exhaustive-turan-scan cpp/exhaustive-turan-scan.cpp -lgmpxx -lgmp
	/tmp/exhaustive-turan-scan 1200
	$(MAKE) audit-independent

export-independent-witnesses:
	KRAW_EXPORT_WITNESS=certificates/independent-odd-minimum.txt python3 -u scripts/odd-minimum-gap.py
	KRAW_EXPORT_WITNESS=certificates/independent-finite-offset.txt python3 -u scripts/finite-gap-offsets.py 14
	KRAW_EXPORT_WITNESS=certificates/independent-fixed-argument.txt python3 -u scripts/fixed-argument-strips.py 12 14

independent-check:
	g++ -std=c++17 -O2 -fopenmp -Wall -Wextra -Werror -pedantic -o /tmp/independent-certificate-check cpp/independent-certificate-check.cpp
	/tmp/independent-certificate-check \
		certificates/independent-odd-minimum.txt \
		certificates/independent-fixed-argument.txt \
		certificates/independent-finite-offset.txt

independent-scan:
	g++ -std=c++17 -O2 -fopenmp -Wall -Wextra -Werror -pedantic -o /tmp/independent-pascal-scan cpp/independent-pascal-scan.cpp
	/tmp/independent-pascal-scan 1200

mutation-test:
	scripts/mutation-test-independent.sh
	scripts/mutation-test-certificates.sh

audit-independent: independent-check independent-scan mutation-test

replay-profile:
	/usr/bin/time -v $(MAKE) replay-all

pdf-preflight: paper
	qpdf --check paper/krawtchouk_turan_positivity.pdf
	pdfinfo paper/krawtchouk_turan_positivity.pdf
	pdffonts paper/krawtchouk_turan_positivity.pdf
	! grep -E "Overfull|undefined|Citation.*undefined|Reference.*undefined" paper/krawtchouk_turan_positivity.log
