#!/bin/sh
set -eu

binary="$(mktemp /tmp/independent-certificate-check.XXXXXX)"
trap 'rm -f "$binary"' EXIT HUP INT TERM

g++ -std=c++17 -O2 -fopenmp -Wall -Wextra -Werror -pedantic \
    -o "$binary" cpp/independent-certificate-check.cpp

odd=certificates/independent-odd-minimum.txt
fixed=certificates/independent-fixed-argument.txt
finite=certificates/independent-finite-offset.txt

OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}" "$binary" \
    "$odd" "$fixed" "$finite" >/dev/null

expect_rejected() {
    mutation="$1"
    witness="$2"
    output="$(mktemp /tmp/independent-certificate-mutation.XXXXXX)"
    if OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}" \
            "$binary" "$witness" --mutation="$mutation" \
            >"$output" 2>&1; then
        printf 'MUTATION SURVIVED: %s\n' "$mutation" >&2
        sed -n '1,160p' "$output" >&2
        rm -f "$output"
        exit 1
    fi
    printf 'mutation rejected: %s\n' "$mutation"
    rm -f "$output"
}

expect_rejected odd-sign "$odd"
expect_rejected fixed-content "$fixed"
expect_rejected fixed-ratio "$fixed"
expect_rejected finite-recurrence "$finite"
expect_rejected finite-factor "$finite"
expect_rejected resultant "$finite"
expect_rejected resultant-link "$finite"

printf 'MUTATION PASS: 7/7 symbolic-certificate corruptions rejected\n'
