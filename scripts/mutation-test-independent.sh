#!/bin/sh
set -eu

binary="$(mktemp /tmp/independent-pascal-scan.XXXXXX)"
trap 'rm -f "$binary"' EXIT HUP INT TERM

g++ -std=c++17 -O2 -fopenmp -Wall -Wextra -Werror -pedantic \
    -o "$binary" cpp/independent-pascal-scan.cpp

OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}" "$binary" 12 none >/dev/null 2>&1

expect_rejected() {
    mutation="$1"
    output="$(mktemp /tmp/independent-pascal-mutation.XXXXXX)"
    if OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}" \
            "$binary" 12 "$mutation" >"$output" 2>&1; then
        printf 'MUTATION SURVIVED: %s\n' "$mutation" >&2
        sed -n '1,120p' "$output" >&2
        rm -f "$output"
        exit 1
    fi
    printf 'mutation rejected: %s\n' "$mutation"
    rm -f "$output"
}

expect_rejected plus-parent
expect_rejected minus-parent
expect_rejected endpoint
expect_rejected turan-gate
expect_rejected cell-count

printf 'MUTATION PASS: 5/5 independent-scan corruptions rejected\n'
