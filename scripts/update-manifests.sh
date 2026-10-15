#!/usr/bin/env sh
# Regenerate certificates/PAYLOAD.sha256, print its digest into the manuscript,
# rebuild the PDF, and regenerate certificates/MANIFEST.sha256 (every tracked
# file except the manifest itself).  Run from the repository root after all
# other changes are staged or committed.
# Usage: scripts/update-manifests.sh   (-h/--help prints this text)
set -eu
# Sort file lists bytewise, independent of the caller's locale.
export LC_ALL=C
case "${1:-}" in -h|--help) sed -n '2,6p' "$0"; exit 0;; esac

payload="LICENSE Makefile requirements.txt environment/Dockerfile
environment/README.md environment/ubuntu.sources certificates/README.md
certificates/CERTIFICATE_MAP.md certificates/REVIEW_CHECKLIST.md
$(git ls-files 'certificates/*.txt' | sort)
$(git ls-files 'scripts/*' | sort)
lean/lakefile.toml lean/lean-toolchain lean/lake-manifest.json lean/Kraw.lean
lean/CheckAxioms.lean $(git ls-files 'lean/Kraw/*.lean' 'lean/tools/*' | sort)"
# shellcheck disable=SC2086
sha256sum $payload > certificates/PAYLOAD.sha256
digest=$(sha256sum certificates/PAYLOAD.sha256 | cut -d' ' -f1)
sed -i "s|\\\\nolinkurl{[0-9a-fA-FA-Z]*}|\\\\nolinkurl{$digest}|" paper/krawtchouk_turan_positivity.tex
echo "payload digest: $digest"
make paper > /dev/null
git ls-files | grep -vx 'certificates/MANIFEST.sha256' | sort | xargs sha256sum > certificates/MANIFEST.sha256
echo "manifest: $(wc -l < certificates/MANIFEST.sha256) files"
