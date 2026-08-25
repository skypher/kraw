// Exhaustive verification of Turan-step positivity for binary Krawtchouk values.
//   T_s(M,Q) = p_s^2 + p_s p_{s+2} - p_{s+1}^2 - p_{s-1} p_{s+1} >= 0
// for all s >= (M+Q)/2, where p_s = [w^s](1+w)^M (1-w)^Q, over all
// (M, Q) with M + Q <= DMAX.  Exact GMP integers; p built by the
// certified step-1 recurrence (s+1) p_{s+1} = (M-Q) p_s + (s-1-M-Q)
// p_{s-1} (exact division), anchored at p_0 = 1, p_1 = M - Q, and
// cross-checked against the binomial convolution for all small rows and
// deterministic coefficients in selected larger rows.
//
// Build: g++ -O2 -fopenmp -o exhaustive-turan-scan exhaustive-turan-scan.cpp -lgmpxx -lgmp
// Usage: ./exhaustive-turan-scan [DMAX=1200]
//   (default matches the manuscript's Proposition; the argument is
//   validated -- a malformed or nonpositive value aborts rather than
//   silently scanning an empty range)
#include <gmpxx.h>
#include <omp.h>
#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <array>
#include <vector>

static mpz_class binom_ui(unsigned long n, unsigned long k) {
    mpz_class out;
    mpz_bin_uiui(out.get_mpz_t(), n, k);
    return out;
}

static mpz_class convolution_coeff(int M, int Q, int s) {
    mpz_class out = 0;
    for (int a = 0; a <= M; ++a) {
        int b = s - a;
        if (0 <= b && b <= Q) {
            mpz_class term = binom_ui(M, a) * binom_ui(Q, b);
            if (b & 1) term = -term;
            out += term;
        }
    }
    return out;
}

static bool audit_row(int M, int Q) {
    // Deterministic larger rows, in addition to the complete D <= 12 check.
    // A row is audited only when it belongs to the requested DMAX range.
    static constexpr std::array<std::array<int, 2>, 6> rows{{
        {{97, 31}}, {{31, 97}}, {{181, 76}},
        {{421, 179}}, {{801, 399}}, {{399, 801}}
    }};
    for (const auto& row : rows)
        if (M == row[0] && Q == row[1]) return true;
    return false;
}

int main(int argc, char** argv) {
    int DMAX = 1200;
    if (argc > 1) {
        char* end = nullptr;
        errno = 0;
        long val = strtol(argv[1], &end, 10);
        if (errno != 0 || end == argv[1] || *end != '\0'
                || val <= 0 || val > 2000000) {
            fprintf(stderr, "invalid DMAX argument: %s\n", argv[1]);
            return 6;
        }
        DMAX = static_cast<int>(val);
    }
    long long neg = 0, checked = 0, division_checks = 0, audit_checks = 0;
    int structural_fail = 0;
    int completed_rows = 0;

#pragma omp parallel for schedule(dynamic, 1) reduction(+:neg, checked, division_checks, audit_checks) reduction(max:structural_fail)
    for (int M = 0; M <= DMAX; M++) {
        std::vector<mpz_class> p;
        for (int Q = 0; M + Q <= DMAX; Q++) {
            int D = M + Q;
            p.assign(D + 3, 0);
            p[0] = 1;
            if (D >= 1) p[1] = M - Q;
            bool row_ok = true;
            for (int s = 1; s < D; s++) {
                // p_{s+1} = [(M-Q) p_s + (s-1-D) p_{s-1}] / (s+1)
                mpz_class num = (M - Q) * p[s] + (s - 1 - D) * p[s - 1];
                division_checks++;
                if (!mpz_divisible_ui_p(num.get_mpz_t(), s + 1)) {
                    structural_fail = 4;
#pragma omp critical
                    gmp_fprintf(stderr,
                                "DIVISIBILITY FAIL at M=%d Q=%d s=%d: %Zd not divisible by %d\n",
                                M, Q, s, num.get_mpz_t(), s + 1);
                    row_ok = false;
                    break;
                }
                mpz_divexact_ui(p[s + 1].get_mpz_t(), num.get_mpz_t(), s + 1);
            }
            // an incomplete row would only produce spurious secondary
            // diagnostics; the nonzero structural_fail already forces a
            // failing exit
            if (!row_ok) continue;
            // sanity: top coefficient = (-1)^Q
            if (p[D] != ((Q & 1) ? -1 : 1)) {
                structural_fail = 2;
#pragma omp critical
                fprintf(stderr, "ANCHOR FAIL at M=%d Q=%d\n", M, Q);
                continue;
            }
            // Independent exact check of the recurrence-built values against
            // the defining binomial convolution on a fixed small region.
            if (D <= 12) {
                for (int s = 0; s <= D; ++s) {
                    audit_checks++;
                    if (p[s] != convolution_coeff(M, Q, s)) {
                        structural_fail = 3;
#pragma omp critical
                        fprintf(stderr,
                                "CONVOLUTION FAIL at M=%d Q=%d s=%d\n",
                                M, Q, s);
                    }
                }
            }
            if (audit_row(M, Q)) {
                const std::array<int, 5> indices{{
                    0, D / 4, D / 2, (3 * D) / 4, D
                }};
                for (int s : indices) {
                    audit_checks++;
                    if (p[s] != convolution_coeff(M, Q, s)) {
                        structural_fail = 5;
#pragma omp critical
                        fprintf(stderr,
                                "LARGE-ROW CONVOLUTION FAIL at M=%d Q=%d s=%d\n",
                                M, Q, s);
                    }
                }
            }
            auto pv = [&](int k) -> mpz_class {
                if (k < 0) return 0;
                if (k > D) return 0;
                return p[k];
            };
            for (int s = (D + 1) / 2; s <= D; s++) {
                mpz_class T = pv(s) * pv(s) + pv(s) * pv(s + 2)
                            - pv(s + 1) * pv(s + 1) - pv(s - 1) * pv(s + 1);
                checked++;
                if (T < 0) {
                    neg++;
#pragma omp critical
                    gmp_printf("T<0 at M=%d Q=%d s=%d: %Zd\n", M, Q, s,
                               T.get_mpz_t());
                }
            }
        }
        int done;
#pragma omp atomic capture
        done = ++completed_rows;
        if (done % 50 == 0 || done == DMAX + 1)
            fprintf(stderr, "completed M-rows: %d/%d\n", done, DMAX + 1);
    }
    if (structural_fail) return structural_fail;
    // the total cell count is asserted, not merely printed: it must
    // equal sum_{D=0}^{DMAX} (D+1)(floor(D/2)+1)
    long long expected_cells = 0;
    for (long long D = 0; D <= DMAX; D++)
        expected_cells += (D + 1) * (D / 2 + 1);
    printf("structural checks: %lld exact divisions; %lld convolution "
           "coefficients\n", division_checks, audit_checks);
    printf("Turan scan D <= %d: %lld cells (expected %lld), negatives %lld\n",
           DMAX, checked, expected_cells, neg);
    if (checked != expected_cells) {
        printf("CELL-COUNT FAIL: %lld != %lld\n", checked, expected_cells);
        return 7;
    }
    if (neg == 0)
        printf("ALL NONNEGATIVE: Turan-step positivity verified for all "
               "D <= %d\n", DMAX);
    return neg ? 1 : 0;
}
