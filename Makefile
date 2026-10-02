override SOURCE_DATE_EPOCH := 1790899200
export SOURCE_DATE_EPOCH
export FORCE_SOURCE_DATE = 1

PROGRAMS := recurrence-and-small-scan regime-decomposition even-minimum-gap odd-minimum-gap

.PHONY: paper verify payload-check toolchain-info replay audit-fast lean pdf-preflight

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

# Run every verification program and compare its output with the committed log.
replay:
	@set -e; for n in $(PROGRAMS); do \
	  echo "== $$n"; \
	  python3 -u scripts/$$n.py | diff -u certificates/$$n.txt -; \
	done; echo "== all replays match the committed logs"

audit-fast: verify toolchain-info replay

# Build the formalization, then require that the final theorems use only the
# standard axioms (in particular no sorryAx).
lean:
	cd lean && lake build Kraw
	cd lean && lake env lean CheckAxioms.lean > .lake/axioms.txt
	cat lean/.lake/axioms.txt
	tr '\n' ' ' < lean/.lake/axioms.txt | grep -oE 'depends on axioms: \[[^]]*\]|does not depend on any axioms' > lean/.lake/axioms-flat.txt
	test "$$(wc -l < lean/.lake/axioms-flat.txt)" -eq "$$(grep -c '^#print axioms' lean/CheckAxioms.lean)"
	! grep 'depends on axioms' lean/.lake/axioms-flat.txt | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' \
	  | sed 's/^ *//;s/ *$$//' | grep -vxE 'propext|Classical.choice|Quot.sound'

pdf-preflight: paper
	qpdf --check paper/krawtchouk_turan_positivity.pdf
	pdfinfo paper/krawtchouk_turan_positivity.pdf
	pdffonts paper/krawtchouk_turan_positivity.pdf
	! grep -E "Overfull|undefined|Citation.*undefined|Reference.*undefined" paper/krawtchouk_turan_positivity.log
