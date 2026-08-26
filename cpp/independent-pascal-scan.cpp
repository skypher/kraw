// Independent exact scan of the Turan-step inequality.
//
// This program deliberately does not reuse either decisive implementation
// choice of cpp/exhaustive-turan-scan.cpp:
//   * integers are boost::multiprecision::cpp_int, rather than GMP integers;
//   * coefficients are constructed across the (M,Q) Pascal lattice, rather
//     than along a row with the Krawtchouk three-term recurrence.
//
// For D=M+Q, a row has two independent parents whenever M,Q>0:
//
//   p(M,Q) = (1+w) p(M-1,Q) = (1-w) p(M,Q-1).
//
// The first equality constructs the row and the second is checked coefficient
// by coefficient.  Endpoint rows use their sole parent.  Reflection and both
// endpoint coefficients are checked before any Turan cell is accepted.
//
// Build:
//   g++ -O2 -fopenmp -o independent-pascal-scan
//       cpp/independent-pascal-scan.cpp
// Usage:
//   ./independent-pascal-scan [DMAX=1200] [mutation=none]
//
// The non-none mutation modes are only for tests/mutation-test-independent.sh.
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <atomic>
#include <cerrno>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

using boost::multiprecision::cpp_int;

enum class Mutation {
    none,
    plus_parent,
    minus_parent,
    endpoint,
    turan_gate,
    cell_count,
};

static const char* mutation_name(Mutation mutation) {
    switch (mutation) {
        case Mutation::none: return "none";
        case Mutation::plus_parent: return "plus-parent";
        case Mutation::minus_parent: return "minus-parent";
        case Mutation::endpoint: return "endpoint";
        case Mutation::turan_gate: return "turan-gate";
        case Mutation::cell_count: return "cell-count";
    }
    return "invalid";
}

static bool parse_mutation(const char* text, Mutation& mutation) {
    if (std::strcmp(text, "none") == 0) mutation = Mutation::none;
    else if (std::strcmp(text, "plus-parent") == 0)
        mutation = Mutation::plus_parent;
    else if (std::strcmp(text, "minus-parent") == 0)
        mutation = Mutation::minus_parent;
    else if (std::strcmp(text, "endpoint") == 0)
        mutation = Mutation::endpoint;
    else if (std::strcmp(text, "turan-gate") == 0)
        mutation = Mutation::turan_gate;
    else if (std::strcmp(text, "cell-count") == 0)
        mutation = Mutation::cell_count;
    else return false;
    return true;
}

static void report_failure(std::atomic<int>& reports, const char* kind,
                           int D, int Q, int s) {
    const int report = reports.fetch_add(1, std::memory_order_relaxed);
    if (report < 12) {
#pragma omp critical(independent_scan_diagnostic)
        {
            std::fprintf(stderr, "%s at D=%d M=%d Q=%d s=%d\n",
                         kind, D, D - Q, Q, s);
            std::fflush(stderr);
        }
    }
}

int main(int argc, char** argv) {
    int DMAX = 1200;
    if (argc > 1) {
        char* end = nullptr;
        errno = 0;
        const long value = std::strtol(argv[1], &end, 10);
        if (errno != 0 || end == argv[1] || *end != '\0'
                || value <= 0 || value > 5000) {
            std::fprintf(stderr, "invalid DMAX argument: %s\n", argv[1]);
            return 6;
        }
        DMAX = static_cast<int>(value);
    }

    Mutation mutation = Mutation::none;
    if (argc > 2 && !parse_mutation(argv[2], mutation)) {
        std::fprintf(stderr, "invalid mutation argument: %s\n", argv[2]);
        return 6;
    }
    if (argc > 3) {
        std::fprintf(stderr, "usage: %s [DMAX] [mutation]\n", argv[0]);
        return 6;
    }
    if (mutation != Mutation::none && DMAX < 8) {
        std::fprintf(stderr, "mutation tests require DMAX >= 8\n");
        return 6;
    }

    std::fprintf(stderr,
                 "independent scan: backend=boost::cpp_int, "
                 "construction=two-parent Pascal, DMAX=%d, mutation=%s\n",
                 DMAX, mutation_name(mutation));
    std::fflush(stderr);

    // Degree zero: p(0,0)=(1).  The outer vector is indexed by Q on the
    // current D-diagonal.
    std::vector<std::vector<cpp_int>> previous(1);
    previous[0].push_back(1);

    long long checked = 0;
    long long expected_cells = 1;
    long long parent_checks = 0;
    long long reflection_checks = 1;
    long long endpoint_checks = 2;
    long long negatives = 0;
    int structural_fail = 0;
    std::atomic<int> reports{0};

    // Evaluate the degree-zero row through the same formula rather than
    // crediting its single cell only through the closed-form count.
    const cpp_int initial_T = previous[0][0]*previous[0][0];
    ++checked;
    if (initial_T < 0) {
        ++negatives;
        report_failure(reports, "NEGATIVE TURAN STEP", 0, 0, 0);
    }
    if (previous[0][0] != 1) structural_fail = 2;
    const auto start = std::chrono::steady_clock::now();

    for (int D = 1; D <= DMAX; ++D) {
        std::vector<std::vector<cpp_int>> current(D + 1);
        long long diagonal_checked = 0;
        long long diagonal_parent_checks = 0;
        long long diagonal_reflection_checks = 0;
        long long diagonal_endpoint_checks = 0;
        long long diagonal_negatives = 0;
        int diagonal_structural_fail = 0;

#pragma omp parallel for schedule(dynamic, 1) \
    reduction(+:diagonal_checked, diagonal_parent_checks, \
                 diagonal_reflection_checks, diagonal_endpoint_checks, \
                 diagonal_negatives) \
    reduction(max:diagonal_structural_fail)
        for (int Q = 0; Q <= D; ++Q) {
            const bool has_plus_parent = Q < D;
            const bool has_minus_parent = Q > 0;
            std::vector<cpp_int> row(D + 1);

            if (has_plus_parent) {
                const std::vector<cpp_int>& parent = previous[Q];
                for (int s = 0; s <= D; ++s) {
                    if (s < D) row[s] += parent[s];
                    if (s > 0) row[s] += parent[s - 1];
                }
            } else {
                const std::vector<cpp_int>& parent = previous[Q - 1];
                for (int s = 0; s <= D; ++s) {
                    if (s < D) row[s] += parent[s];
                    if (s > 0) row[s] -= parent[s - 1];
                }
            }

            if (mutation == Mutation::plus_parent
                    && D == 8 && Q == 3)
                row[4] += 1;

            // Interior rows are recomputed from the other parent.  This is
            // an identity check, not a sample: every coefficient is tested.
            if (has_plus_parent && has_minus_parent) {
                const std::vector<cpp_int>& parent = previous[Q - 1];
                for (int s = 0; s <= D; ++s) {
                    cpp_int alternate = 0;
                    if (s < D) alternate += parent[s];
                    if (s > 0) alternate -= parent[s - 1];
                    if (mutation == Mutation::minus_parent
                            && D == 8 && Q == 3 && s == 4)
                        alternate += 1;
                    ++diagonal_parent_checks;
                    if (row[s] != alternate) {
                        diagonal_structural_fail = 1;
                        report_failure(reports, "PARENT MISMATCH", D, Q, s);
                    }
                }
            }

            if (mutation == Mutation::endpoint && D == 8 && Q == 3)
                row[D] += 1;

            ++diagonal_endpoint_checks;
            if (row[0] != 1) {
                diagonal_structural_fail = 2;
                report_failure(reports, "LOW-ENDPOINT FAIL", D, Q, 0);
            }
            ++diagonal_endpoint_checks;
            const cpp_int expected_top = (Q & 1) ? cpp_int(-1) : cpp_int(1);
            if (row[D] != expected_top) {
                diagonal_structural_fail = 2;
                report_failure(reports, "TOP-ENDPOINT FAIL", D, Q, D);
            }

            const bool odd_Q = (Q & 1) != 0;
            for (int s = 0; s <= D; ++s) {
                ++diagonal_reflection_checks;
                const cpp_int reflected = odd_Q ? -row[s] : row[s];
                if (row[D - s] != reflected) {
                    diagonal_structural_fail = 3;
                    report_failure(reports, "REFLECTION FAIL", D, Q, s);
                }
            }

            for (int s = (D + 1) / 2; s <= D; ++s) {
                cpp_int T = row[s] * row[s];
                if (s + 2 <= D) T += row[s] * row[s + 2];
                if (s + 1 <= D) {
                    T -= row[s + 1] * row[s + 1];
                    if (s > 0) T -= row[s - 1] * row[s + 1];
                }
                if (mutation == Mutation::turan_gate
                        && D == 4 && Q == 0 && s == 2)
                    T = -1;
                if (!(mutation == Mutation::cell_count
                        && D == 4 && Q == 0 && s == 2))
                    ++diagonal_checked;
                if (T < 0) {
                    ++diagonal_negatives;
                    report_failure(reports, "NEGATIVE TURAN STEP", D, Q, s);
                }
            }
            current[Q] = std::move(row);
        }

        structural_fail = std::max(structural_fail,
                                   diagonal_structural_fail);
        checked += diagonal_checked;
        parent_checks += diagonal_parent_checks;
        reflection_checks += diagonal_reflection_checks;
        endpoint_checks += diagonal_endpoint_checks;
        negatives += diagonal_negatives;
        expected_cells += static_cast<long long>(D + 1) * (D / 2 + 1);
        previous = std::move(current);

        if (D % 25 == 0 || D == DMAX) {
            const double elapsed = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - start).count();
            std::fprintf(stderr,
                         "completed diagonals: %d/%d; cells=%lld; "
                         "parent_checks=%lld; elapsed_seconds=%.1f\n",
                         D, DMAX, checked, parent_checks, elapsed);
            std::fflush(stderr);
        }
    }

    std::printf("independent structural checks: %lld alternate-parent "
                "coefficients; %lld reflections; %lld endpoints\n",
                parent_checks, reflection_checks, endpoint_checks);
    std::printf("independent Turan scan D <= %d: %lld cells "
                "(expected %lld), negatives %lld\n",
                DMAX, checked, expected_cells, negatives);
    if (structural_fail != 0) {
        std::printf("STRUCTURAL CHECK FAIL: code %d\n", structural_fail);
        return 10 + structural_fail;
    }
    if (checked != expected_cells) {
        std::printf("CELL-COUNT FAIL: %lld != %lld\n",
                    checked, expected_cells);
        return 7;
    }
    if (negatives != 0) return 1;
    std::printf("INDEPENDENT PASS: all cells nonnegative for D <= %d\n",
                DMAX);
    return 0;
}
