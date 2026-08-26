// Independent replay of the exported symbolic witnesses.
//
// This checker uses only boost::multiprecision::cpp_int and the small exact
// polynomial/Sturm implementation in exact-polynomial.hpp.  In particular it
// neither imports nor links SymPy, GMP, or another computer-algebra system.
//
// Build:
//   g++ -std=c++17 -O2 -fopenmp -o independent-certificate-check
//       cpp/independent-certificate-check.cpp
// Usage:
//   ./independent-certificate-check WITNESS... [--mutation=NAME]
#include "exact-polynomial.hpp"

#include <algorithm>
#include <atomic>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

using namespace kraw_exact;

struct Metadata {
    std::string kind;
    std::vector<std::string> field;
};

struct Document {
    std::string suite;
    std::map<std::string, Polynomial> polynomial;
    std::vector<Metadata> metadata;
};

static std::vector<std::string> split_words(const std::string& line) {
    std::istringstream stream(line);
    std::vector<std::string> words;
    std::string word;
    while (stream >> word) words.push_back(word);
    return words;
}

static cpp_int parse_integer(const std::string& text) {
    std::istringstream stream(text);
    cpp_int value;
    stream >> value;
    if (!stream || !stream.eof())
        throw std::runtime_error("invalid exact integer: " + text);
    return value;
}

static int parse_int(const std::string& text) {
    std::size_t used = 0;
    const long value = std::stol(text, &used);
    if (used != text.size()) throw std::runtime_error("invalid integer: " + text);
    return static_cast<int>(value);
}

static Document read_document(const std::string& path) {
    std::ifstream input(path);
    if (!input) throw std::runtime_error("cannot open witness: " + path);
    std::string line;
    if (!std::getline(input, line)) throw std::runtime_error("empty witness: " + path);
    const std::vector<std::string> header = split_words(line);
    if (header.size() != 2 || header[0] != "KRAW_WITNESS_V1")
        throw std::runtime_error("bad witness header: " + path);
    Document document;
    document.suite = header[1];
    bool ended = false;
    while (std::getline(input, line)) {
        if (line.empty()) continue;
        const std::vector<std::string> words = split_words(line);
        if (words.empty()) continue;
        if (words[0] == "END") {
            if (words.size() != 1) throw std::runtime_error("malformed END line");
            ended = true;
            break;
        }
        if (words[0] == "META") {
            if (words.size() < 2) throw std::runtime_error("malformed META line");
            Metadata metadata;
            metadata.kind = words[1];
            metadata.field.assign(words.begin() + 2, words.end());
            document.metadata.push_back(std::move(metadata));
            continue;
        }
        if (words[0] != "POLY" || words.size() < 5)
            throw std::runtime_error("malformed witness line: " + line);
        const std::string name = words[1];
        const int arity = parse_int(words[2]);
        if (static_cast<int>(words.size()) != 4 + arity)
            throw std::runtime_error("malformed POLY header: " + line);
        const int term_count = parse_int(words[3 + arity]);
        Polynomial polynomial(arity);
        for (int term_index = 0; term_index < term_count; ++term_index) {
            if (!std::getline(input, line))
                throw std::runtime_error("truncated polynomial: " + name);
            const std::vector<std::string> term = split_words(line);
            if (static_cast<int>(term.size()) != arity + 3 || term[0] != "TERM")
                throw std::runtime_error("malformed TERM in " + name);
            Monomial monomial;
            for (int variable = 0; variable < arity; ++variable)
                monomial.exponent[variable] = parse_int(term[1 + variable]);
            const cpp_int numerator = parse_integer(term[1 + arity]);
            const cpp_int denominator = parse_integer(term[2 + arity]);
            polynomial.add_term(monomial, Rational(numerator, denominator));
        }
        if (!document.polynomial.emplace(name, std::move(polynomial)).second)
            throw std::runtime_error("duplicate polynomial: " + name);
    }
    if (!ended) throw std::runtime_error("witness has no END marker: " + path);
    while (std::getline(input, line))
        if (!split_words(line).empty())
            throw std::runtime_error("data after END in witness: " + path);
    return document;
}

static Polynomial& named(Document& document, const std::string& name) {
    auto found = document.polynomial.find(name);
    if (found == document.polynomial.end())
        throw std::runtime_error("missing polynomial: " + name);
    return found->second;
}

static const Polynomial& named(const Document& document, const std::string& name) {
    auto found = document.polynomial.find(name);
    if (found == document.polynomial.end())
        throw std::runtime_error("missing polynomial: " + name);
    return found->second;
}

struct CheckState {
    int checks{0};
    int failures{0};

    void require(bool condition, const std::string& description) {
        ++checks;
        if (!condition) {
            ++failures;
            std::cerr << "  [FAIL] " << description << "\n";
        }
    }
};

static bool coefficients_nonnegative(const Polynomial& polynomial,
                                     bool require_nonzero = true) {
    if (require_nonzero && polynomial.is_zero()) return false;
    for (const auto& item : polynomial.terms)
        if (item.second.sign() < 0) return false;
    return true;
}

static bool nonnegative_region_certificate(const Polynomial& source,
                                           int lower_u, int strip_high,
                                           int split_u, int lower_D) {
    if (source.arity != 2) return false;
    const Polynomial w = Polynomial::variable(2, 0);
    const Polynomial v = Polynomial::variable(2, 1);
    const Polynomial u_image = w + Polynomial::constant(2, Rational(split_u));
    const Polynomial D_image = pow_poly(u_image, 2)*Rational(24)
                             + v - Polynomial::constant(2, Rational(3));
    const Polynomial large = substitute(source, {D_image, u_image});
    if (!coefficients_nonnegative(large)) return false;

    const Polynomial ray_variable = Polynomial::variable(1, 0);
    const Polynomial D_ray = ray_variable
                           + Polynomial::constant(1, Rational(lower_D));
    for (int fixed_u = lower_u; fixed_u <= strip_high; ++fixed_u) {
        const Polynomial u_constant =
            Polynomial::constant(1, Rational(fixed_u));
        const Polynomial strip = substitute(source, {D_ray, u_constant});
        if (coefficients_nonnegative(strip)) continue;
        if (!positive_on_ray(as_univariate(strip), Rational(0))) return false;
    }
    return true;
}

static void check_odd_minimum(const Document& document, CheckState& state) {
    std::cout << "== independent odd-minimum witnesses ==\n";
    int ray_count = 0;
    int region_count = 0;
    std::set<std::string> ray_names;
    std::set<std::string> region_names;
    for (const Metadata& metadata : document.metadata) {
        if (metadata.kind == "RAY_POS") {
            if (metadata.field.size() != 3)
                throw std::runtime_error("malformed RAY_POS metadata");
            const Polynomial& polynomial = named(document, metadata.field[0]);
            const int onset = parse_int(metadata.field[1]);
            const int expected_sign = parse_int(metadata.field[2]);
            const Univariate univariate = as_univariate(polynomial);
            const bool ok = expected_sign > 0
                ? positive_on_ray(univariate, Rational(onset))
                : positive_on_ray(-univariate, Rational(onset));
            state.require(ok, "ray sign: " + metadata.field[0]);
            ray_names.insert(metadata.field[0]);
            ++ray_count;
        } else if (metadata.kind == "REGION_POS") {
            if (metadata.field.size() != 5)
                throw std::runtime_error("malformed REGION_POS metadata");
            const Polynomial& polynomial = named(document, metadata.field[0]);
            const bool ok = nonnegative_region_certificate(
                polynomial, parse_int(metadata.field[1]),
                parse_int(metadata.field[2]), parse_int(metadata.field[3]),
                parse_int(metadata.field[4]));
            state.require(ok, "region sign: " + metadata.field[0]);
            region_names.insert(metadata.field[0]);
            ++region_count;
        }
    }
    state.require(ray_count == 4,
                  "odd-minimum witness has two base numerators and denominators");
    state.require(region_count == 4,
                  "odd-minimum witness has four infinite-region obligations");
    state.require(ray_names == std::set<std::string>{
                      "odd_base_num_0", "odd_base_den_0",
                      "odd_base_num_1", "odd_base_den_1"},
                  "odd-minimum base witness names are complete");
    state.require(region_names == std::set<std::string>{
                      "odd_region_O1", "odd_region_O2",
                      "odd_region_O3", "odd_region_O4"},
                  "odd-minimum region witness names are complete");
    if (state.failures == 0)
        std::cout << "  [PASS] 2 base rays (numerator/denominator) and "
                     "4 region obligations\n";
}

static Polynomial lift_first(const Polynomial& source) {
    if (source.arity != 1) throw std::runtime_error("lift expects one variable");
    Polynomial result(2);
    for (const auto& item : source.terms) {
        Monomial monomial;
        monomial.exponent[0] = item.first.exponent[0];
        result.add_term(monomial, item.second);
    }
    return result;
}

static long long binomial_small(int n, int k) {
    if (k < 0 || k > n) return 0;
    k = std::min(k, n - k);
    long long result = 1;
    for (int index = 1; index <= k; ++index)
        result = result*(n - k + index)/index;
    return result;
}

static Rational fixed_ratio_shift(int Q, int shift,
                                  const Rational& D, const Rational& u) {
    const Rational M = D - Rational(Q);
    const Rational s = (D + u)/Rational(2);
    Rational total(0);
    for (int b = 0; b <= Q; ++b) {
        const int displacement = shift - b;
        Rational term(1);
        if (displacement >= 0) {
            for (int index = 0; index < displacement; ++index)
                term = term*(M - s - Rational(index))
                           /(s + Rational(index + 1));
        } else {
            for (int index = 0; index < -displacement; ++index)
                term = term*(s - Rational(index))
                           /(M - s + Rational(index + 1));
        }
        term = term*Rational(binomial_small(Q, b));
        if (b & 1) term = -term;
        total = total + term;
    }
    return total;
}

static int ratio_denominator_degree_bound(int Q, int shift) {
    int result = 0;
    for (int b = 0; b <= Q; ++b) result += std::abs(shift - b);
    return result;
}

static bool fixed_ratio_identity_grid(const Polynomial& numerator,
                                      const Polynomial& denominator,
                                      int Q, int shift) {
    // The defining finite sum has a common-denominator representation of
    // total degree L_j=sum_b |j-b|.  After cross multiplication with the
    // exported reduced fraction, the difference has total degree at most the
    // bound below.  The full square grid is consequently an exact identity
    // certificate.
    const int bound = ratio_denominator_degree_bound(Q, shift)
        + std::max(numerator.total_degree(), denominator.total_degree());
    const int grid_side = bound + 1;
    const long long base_D = 4LL*bound + 2000;
    std::atomic<int> completed_rows{0};
    int failed = 0;

#pragma omp parallel for schedule(dynamic, 1) reduction(max:failed)
    for (int u_index = 0; u_index < grid_side; ++u_index) {
        const Rational u_value(2LL*u_index);
        for (int D_index = 0; D_index < grid_side; ++D_index) {
            const Rational D_value(base_D + 2LL*D_index);
            const Rational direct = fixed_ratio_shift(
                Q, shift, D_value, u_value);
            const Rational numerator_value =
                numerator.evaluate({D_value, u_value});
            const Rational denominator_value =
                denominator.evaluate({D_value, u_value});
            if (denominator_value.is_zero()
                    || direct != numerator_value/denominator_value) {
                failed = 1;
                break;
            }
        }
        const int done = completed_rows.fetch_add(1) + 1;
        if (done % 25 == 0 || done == grid_side) {
#pragma omp critical(independent_checker_progress)
            {
                std::cerr << "  [progress] fixed Q=" << Q
                          << " ratio " << shift << " rows "
                          << done << "/" << grid_side
                          << " (" << static_cast<long long>(done)*grid_side
                          << " exact grid points)\n";
                std::cerr.flush();
            }
        }
    }
    return failed == 0;
}

struct PolynomialFraction {
    Polynomial numerator;
    Polynomial denominator;
};

static PolynomialFraction fraction_add(const PolynomialFraction& left,
                                       const PolynomialFraction& right) {
    return {left.numerator*right.denominator
              + right.numerator*left.denominator,
            left.denominator*right.denominator};
}

static PolynomialFraction fraction_subtract(const PolynomialFraction& left,
                                            const PolynomialFraction& right) {
    return {left.numerator*right.denominator
              - right.numerator*left.denominator,
            left.denominator*right.denominator};
}

static PolynomialFraction fraction_multiply(const PolynomialFraction& left,
                                            const PolynomialFraction& right) {
    return {left.numerator*right.numerator,
            left.denominator*right.denominator};
}

static long long integer_sqrt(long long value) {
    if (value < 0) throw std::runtime_error("integer square root of negative value");
    constexpr long long largest_root = 3037000499LL;
    long long low = 0;
    long long high = std::min(value, largest_root) + 1;
    while (low + 1 < high) {
        const long long middle = low + (high - low)/2;
        if (middle != 0 && middle <= value/middle) low = middle;
        else high = middle;
    }
    return low;
}

static std::array<int, 3> first_open_gap_cpp(int qmin, int umax,
                                             int stop_D) {
    for (int D = 4; D <= stop_D; ++D) {
        int u = umax + 1;
        if ((D - u) & 1) ++u;
        if (u > D) continue;
        const long long U = static_cast<long long>(u + 1)*(u + 1);
        const long long E = static_cast<long long>(D + 3)*(D + 3);
        const long long upper = static_cast<long long>(D + 1)*(D + 1) - U;
        if (upper <= 0) continue;
        long long x = std::min<long long>(D - 2*qmin,
                                         integer_sqrt(upper - 1));
        if (x < 0) continue;
        if ((x - D) & 1) --x;
        if (x >= 0 && x*x*U > (U - 1)*(E - U))
            return {{D, static_cast<int>((D - x)/2), u}};
    }
    return {{-1, -1, -1}};
}

struct FixedCase {
    int Q{0};
    int D0{0};
    int D0_content{0};
    int degree_u{0};
    std::string S;
    std::string denominator;
    std::string content;
};

static void check_fixed_argument(const Document& document, CheckState& state) {
    std::cout << "== independent fixed-argument witnesses ==\n";
    std::map<int, FixedCase> cases;
    std::map<int, Rational> denominator_constant;
    std::map<int, std::vector<std::pair<std::string, int>>> denominator_factors;
    std::map<int, std::map<int, std::string>> coefficients;
    std::map<int, std::map<int, std::pair<std::string, std::string>>> ratios;
    std::map<int, std::pair<std::string, int>> edges;
    std::vector<Metadata> thresholds;

    for (const Metadata& metadata : document.metadata) {
        const auto& f = metadata.field;
        if (metadata.kind == "FIXED_CASE") {
            if (f.size() != 7) throw std::runtime_error("malformed FIXED_CASE");
            FixedCase item;
            item.Q = parse_int(f[0]);
            item.D0 = parse_int(f[1]);
            item.D0_content = parse_int(f[2]);
            item.degree_u = parse_int(f[3]);
            item.S = f[4];
            item.denominator = f[5];
            item.content = f[6];
            cases[item.Q] = item;
        } else if (metadata.kind == "DEN_CONST") {
            if (f.size() != 3) throw std::runtime_error("malformed DEN_CONST");
            denominator_constant[parse_int(f[0])] =
                Rational(parse_integer(f[1]), parse_integer(f[2]));
        } else if (metadata.kind == "DEN_FACTOR") {
            if (f.size() != 3) throw std::runtime_error("malformed DEN_FACTOR");
            denominator_factors[parse_int(f[0])].push_back(
                {f[1], parse_int(f[2])});
        } else if (metadata.kind == "FIXED_COEFF") {
            if (f.size() != 3) throw std::runtime_error("malformed FIXED_COEFF");
            coefficients[parse_int(f[0])][parse_int(f[1])] = f[2];
        } else if (metadata.kind == "FIXED_RATIO") {
            if (f.size() != 4) throw std::runtime_error("malformed FIXED_RATIO");
            ratios[parse_int(f[0])][parse_int(f[1])] = {f[2], f[3]};
        } else if (metadata.kind == "EDGE_RAY") {
            if (f.size() != 3) throw std::runtime_error("malformed EDGE_RAY");
            edges[parse_int(f[0])] = {f[1], parse_int(f[2])};
        } else if (metadata.kind == "THRESHOLD") {
            thresholds.push_back(metadata);
        }
    }

    bool complete_fixed_range = cases.size() == 10;
    for (int Q = 3; Q <= 12; ++Q)
        complete_fixed_range = complete_fixed_range && cases.count(Q) == 1;
    state.require(complete_fixed_range,
                  "fixed-argument witness contains exactly Q=3,...,12");
    if (!complete_fixed_range) return;
    for (const auto& case_entry : cases) {
        const int failures_before_case = state.failures;
        const FixedCase& item = case_entry.second;
        const Polynomial& S = named(document, item.S);
        const Polynomial& den = named(document, item.denominator);
        const Polynomial& content = named(document, item.content);
        state.require(item.degree_u == 2*item.Q + 1,
                      "Q=" + std::to_string(item.Q) + " numerator degree");
        state.require(content.arity == 1
                      && positive_on_ray(as_univariate(content),
                                         Rational(item.D0_content)),
                      "Q=" + std::to_string(item.Q) + " positive content");

        const auto coefficient_map = coefficients.find(item.Q);
        if (coefficient_map == coefficients.end())
            throw std::runtime_error("missing fixed coefficients");
        Polynomial coefficient_sum(2);
        std::vector<Univariate> cc(item.degree_u + 1);
        std::vector<int> sign(item.degree_u + 1, 0);
        for (int j = 0; j <= item.degree_u; ++j) {
            const auto found = coefficient_map->second.find(j);
            if (found == coefficient_map->second.end())
                throw std::runtime_error("missing fixed coefficient index");
            const Polynomial& coefficient = named(document, found->second);
            cc[j] = as_univariate(coefficient);
            if (!cc[j].is_zero()) sign[j] = cc[j].leading().sign();
            Polynomial lifted = lift_first(coefficient);
            Monomial u_power;
            u_power.exponent[1] = j;
            Polynomial monomial(2);
            monomial.add_term(u_power, Rational(1));
            coefficient_sum = coefficient_sum + lifted*monomial;
        }
        state.require(S == lift_first(content)*coefficient_sum,
                      "Q=" + std::to_string(item.Q)
                      + " content/coefficient identity");

        auto constant_found = denominator_constant.find(item.Q);
        if (constant_found == denominator_constant.end())
            throw std::runtime_error("missing denominator constant");
        Polynomial factor_product = Polynomial::constant(2,
                                                         constant_found->second);
        int denominator_sign = constant_found->second.sign();
        bool factor_classification = denominator_sign != 0;
        const Rational alpha(7, 6*(2*item.Q + 3));
        for (const auto& factor_record : denominator_factors[item.Q]) {
            const Polynomial& factor = named(document, factor_record.first);
            const int multiplicity = factor_record.second;
            factor_product = factor_product*pow_poly(factor, multiplicity);
            if (factor.total_degree() != 1) {
                factor_classification = false;
                continue;
            }
            const Rational aD = factor.coefficient(1, 0);
            const Rational au = factor.coefficient(0, 1);
            const Rational c0 = factor.coefficient(0, 0);
            const Rational lower_slope = aD;
            const Rational lower_onset = aD*Rational(item.D0) + c0;
            const Rational upper_slope = aD + au*alpha;
            const Rational upper_onset =
                aD*Rational(item.D0)
                + au*alpha*Rational(item.D0 + 3) + c0;
            int uniform_sign = 0;
            if (lower_slope.sign() >= 0 && upper_slope.sign() >= 0
                    && lower_onset.sign() > 0
                    && upper_onset.sign() > 0) {
                uniform_sign = 1;
            } else if (lower_slope.sign() <= 0
                    && upper_slope.sign() <= 0
                    && lower_onset.sign() < 0
                    && upper_onset.sign() < 0) {
                uniform_sign = -1;
            } else {
                factor_classification = false;
            }
            if ((multiplicity & 1) != 0)
                denominator_sign *= uniform_sign;
        }
        state.require(factor_product == den,
                      "Q=" + std::to_string(item.Q)
                      + " exported denominator factorization");
        state.require(factor_classification && denominator_sign < 0,
                      "Q=" + std::to_string(item.Q)
                      + " exact wedge denominator sign/nonvanishing");

        std::set<int> used;
        bool pair_ok = true;
        const Polynomial Dvar = Polynomial::variable(1, 0);
        const Polynomial BQ = (Dvar + Polynomial::constant(1, Rational(3)))
                            * alpha;
        for (int j = 0; j <= item.degree_u; ++j) {
            if (sign[j] >= 0) continue;
            if (j < 2 || sign[j - 2] != 1 || used.count(j - 2)) {
                pair_ok = false;
                continue;
            }
            used.insert(j - 2);
            const Polynomial& negative_poly = named(
                document, coefficient_map->second.at(j));
            const Polynomial& partner_poly = named(
                document, coefficient_map->second.at(j - 2));
            const Polynomial endpoint = partner_poly + negative_poly*BQ;
            pair_ok = pair_ok
                && positive_on_ray(-cc[j], Rational(item.D0))
                && positive_on_ray(cc[j - 2], Rational(item.D0))
                && positive_on_ray(as_univariate(endpoint), Rational(item.D0));
        }
        std::set<int> expected;
        if ((item.Q & 1) == 0) {
            for (int r = 0; r < item.Q/2; ++r) {
                expected.insert(4*r);
                expected.insert(4*r + 1);
            }
        } else {
            for (int r = 0; r < (item.Q - 1)/2; ++r) {
                expected.insert(4*r + 2);
                expected.insert(4*r + 3);
            }
        }
        pair_ok = pair_ok && used == expected;
        for (int j = 0; j <= item.degree_u; ++j)
            if (sign[j] == 1)
                pair_ok = pair_ok
                    && positive_on_ray(cc[j], Rational(item.D0));
        state.require(pair_ok,
                      "Q=" + std::to_string(item.Q)
                      + " independent Sturm/pairing certificate");

        const auto edge = edges.find(item.Q);
        if (edge == edges.end()) throw std::runtime_error("missing edge ray");
        state.require(positive_on_ray(as_univariate(named(document, edge->second.first)),
                                      Rational(edge->second.second)),
                      "Q=" + std::to_string(item.Q) + " edge-flow ray");
        if (state.failures != failures_before_case) return;
        const auto ratio_case = ratios.find(item.Q);
        if (ratio_case == ratios.end() || ratio_case->second.size() != 4)
            throw std::runtime_error("missing fixed ratio witnesses");
        std::map<int, PolynomialFraction> fraction;
        bool ratio_identities = true;
        for (int shift : {-1, 0, 1, 2}) {
            const auto record = ratio_case->second.find(shift);
            if (record == ratio_case->second.end())
                throw std::runtime_error("missing fixed ratio shift");
            const Polynomial& numerator = named(document, record->second.first);
            const Polynomial& denominator = named(document, record->second.second);
            ratio_identities = ratio_identities
                && fixed_ratio_identity_grid(numerator, denominator,
                                             item.Q, shift);
            fraction.emplace(shift,
                             PolynomialFraction{numerator, denominator});
        }
        state.require(ratio_identities,
                      "Q=" + std::to_string(item.Q)
                      + " four defining ratio identities");
        if (state.failures != failures_before_case) return;
        const auto fixed_phase = [&](const char* phase) {
            std::cerr << "  [progress] fixed Q=" << item.Q
                      << " fraction-combination phase=" << phase << "\n";
            std::cerr.flush();
        };
        const PolynomialFraction r0_squared = fraction_multiply(
            fraction.at(0), fraction.at(0));
        fixed_phase("r0_squared");
        const PolynomialFraction r0_r2 = fraction_multiply(
            fraction.at(0), fraction.at(2));
        fixed_phase("r0_r2");
        const PolynomialFraction r1_squared = fraction_multiply(
            fraction.at(1), fraction.at(1));
        fixed_phase("r1_squared");
        const PolynomialFraction rm1_r1 = fraction_multiply(
            fraction.at(-1), fraction.at(1));
        fixed_phase("rm1_r1");
        const PolynomialFraction left = fraction_add(r0_squared, r0_r2);
        fixed_phase("left_sum");
        const PolynomialFraction right = fraction_add(r1_squared, rm1_r1);
        fixed_phase("right_sum");
        const PolynomialFraction determinant_difference =
            fraction_subtract(left, right);
        fixed_phase("determinant_difference");
        state.require(
            (determinant_difference.numerator*den
             + S*determinant_difference.denominator).is_zero(),
            "Q=" + std::to_string(item.Q)
            + " ratio combination equals -S/den");
        if (state.failures != failures_before_case) return;
        if (state.failures == 0)
            std::cout << "  [PASS] fixed Q=" << item.Q << "\n";
    }

    state.require(thresholds.size() == 1,
                  "fixed witness contains one threshold census");
    if (thresholds.size() == 1) {
        const auto& f = thresholds.front().field;
        if (f.size() != 5) throw std::runtime_error("malformed THRESHOLD");
        state.require(parse_int(f[0]) == 13 && parse_int(f[1]) == 14
                      && parse_int(f[2]) == 14827
                      && parse_int(f[3]) == 13 && parse_int(f[4]) == 15,
                      "fixed canonical threshold declaration");
        const std::array<int, 3> found = first_open_gap_cpp(
            parse_int(f[0]), parse_int(f[1]), parse_int(f[2]));
        state.require(found == std::array<int, 3>{{
                          parse_int(f[2]), parse_int(f[3]), parse_int(f[4])}},
                      "fixed first-open-gap census");
    }
}

struct FactorRecord {
    std::string polynomial;
    int multiplicity{0};
    int no_root_prime{0};
};

struct FiniteCaseRecord {
    std::string label;
    int u{0};
    int epsilon{0};
    int version{0};
    std::string G, lambda, mu, A, B, C;
    std::string reduced_G, reduced_lambda, reduced_mu, common;
    Rational tmax;
    int expected_M0{0};
};

struct ResultantRecord {
    std::string label;
    std::string first, second, resultant;
    int threshold{0};
    int sector_divisor{0};
};

struct LinearSeedForm {
    Polynomial first;
    Polynomial second;
};

struct QuadraticSeedForm {
    Polynomial first_squared;
    Polynomial cross;
    Polynomial second_squared;
};

struct ReconstructedFiniteCase {
    Polynomial lambda, mu, A, B, C;
};

static LinearSeedForm linear_add(const LinearSeedForm& left,
                                 const LinearSeedForm& right) {
    return {left.first + right.first, left.second + right.second};
}

static LinearSeedForm linear_scale(const Polynomial& scale,
                                   const LinearSeedForm& form) {
    return {scale*form.first, scale*form.second};
}

static void add_quadratic_product(QuadraticSeedForm& target,
                                  const LinearSeedForm& left,
                                  const LinearSeedForm& right,
                                  const Polynomial& scale) {
    target.first_squared = target.first_squared
                         + scale*left.first*right.first;
    target.cross = target.cross
                 + scale*(left.first*right.second
                          + left.second*right.first);
    target.second_squared = target.second_squared
                          + scale*left.second*right.second;
}

static ReconstructedFiniteCase reconstruct_finite_case(int u, int epsilon,
                                                       int version) {
    const Polynomial M = Polynomial::variable(2, 0);
    const Polynomial Q = Polynomial::variable(2, 1);
    const Polynomial D = M + Q;
    const Polynomial x = M - Q;
    const Polynomial k0 =
        (D - Polynomial::constant(2, Rational(u)))/Rational(2);
    const Polynomial zero = Polynomial::constant(2, Rational(0));
    const Polynomial one = Polynomial::constant(2, Rational(1));
    const int low = version == 1 ? 0 : -1;

    std::map<int, LinearSeedForm> P;
    std::map<int, Polynomial> c;
    P.emplace(low, LinearSeedForm{one, zero});
    P.emplace(low + 1, LinearSeedForm{zero, one});
    c.emplace(low, one);
    c.emplace(low + 1, one);
    for (int index = low + 1; index < u + 2; ++index) {
        const Polynomial ratio = index == low + 1
            ? one
            : k0 + Polynomial::constant(2, Rational(index));
        const Polynomial previous_scale =
            (k0 + Polynomial::constant(2, Rational(index - 1)) - D)*ratio;
        P.emplace(index + 1,
            linear_add(linear_scale(x, P.at(index)),
                       linear_scale(previous_scale, P.at(index - 1))));
        c.emplace(index + 1,
            c.at(index)*(k0 + Polynomial::constant(
                2, Rational(index + 1))));
    }

    const int constraint_index = version == 1 ? u : u + 1;
    const Polynomial lambda = P.at(constraint_index).first
        - c.at(constraint_index)*Rational(epsilon);
    const Polynomial mu = P.at(constraint_index).second;

    const auto ratio = [&](int index) {
        return k0 + Polynomial::constant(2, Rational(index));
    };
    const Polynomial scale_uu = pow_poly(ratio(u + 1), 2)*ratio(u + 2);
    const Polynomial scale_u_u2 = ratio(u + 1);
    const Polynomial scale_u1u1 = ratio(u + 2);
    const Polynomial scale_um_u1 = ratio(u)*ratio(u + 1)*ratio(u + 2);
    QuadraticSeedForm quadratic{zero, zero, zero};
    add_quadratic_product(quadratic, P.at(u), P.at(u), scale_uu);
    add_quadratic_product(quadratic, P.at(u), P.at(u + 2), scale_u_u2);
    add_quadratic_product(quadratic, P.at(u + 1), P.at(u + 1),
                          -scale_u1u1);
    add_quadratic_product(quadratic, P.at(u - 1), P.at(u + 1),
                          -scale_um_u1);
    return {lambda, mu, quadratic.first_squared,
            quadratic.cross, quadratic.second_squared};
}

static std::pair<bool, int> positive_core_factor(const Polynomial& factor,
                                                const Rational& tmax) {
    const int degree = factor.total_degree();
    if (degree < 2) return {false, 0};
    std::map<int, Rational> leading_form;
    std::map<int, Rational> lower_sums;
    for (const auto& item : factor.terms) {
        const int M_degree = item.first.exponent[0];
        const int Q_degree = item.first.exponent[1];
        const int deficit = degree - M_degree - Q_degree;
        if (deficit == 0) {
            leading_form[Q_degree] = leading_form[Q_degree] + item.second;
        } else {
            lower_sums[deficit] = lower_sums[deficit]
                + abs_rat(item.second)*pow_rat(tmax, Q_degree);
        }
    }
    Rational derivative_bound(0);
    for (const auto& item : leading_form) {
        if (item.first == 0) continue;
        derivative_bound = derivative_bound
            + abs_rat(item.second)*Rational(item.first)
              *pow_rat(tmax, item.first - 1);
    }
    Rational minimum;
    bool first_value = true;
    constexpr int grid = 512;
    for (int index = 0; index <= grid; ++index) {
        const Rational point = tmax*Rational(index, grid);
        Rational value(0);
        for (const auto& item : leading_form)
            value = value + item.second*pow_rat(point, item.first);
        if (first_value || value < minimum) {
            minimum = value;
            first_value = false;
        }
    }
    const Rational lower = minimum
        - derivative_bound*tmax/Rational(2*grid);
    if (lower.sign() <= 0) return {false, 0};

    const auto dominated = [&](int M0) {
        Rational error(0);
        for (const auto& item : lower_sums)
            error = error + item.second/pow_rat(Rational(M0), item.first);
        return error < lower;
    };
    int high = 2;
    while (!dominated(high)) {
        high *= 2;
        if (high > 1145) return std::pair<bool, int>{false, 0};
    }
    int low = high/2;
    while (low + 1 < high) {
        const int middle = (low + high)/2;
        if (dominated(middle)) high = middle;
        else low = middle;
    }
    return {true, high};
}

static std::pair<bool, int> finite_positive_factorization(
        const Document& document, const Rational& constant,
        const std::vector<FactorRecord>& factors,
        const Rational& tmax) {
    int overall_sign = constant.sign();
    if (overall_sign == 0) return {false, 0};
    int maximum_M0 = 0;
    for (const FactorRecord& record : factors) {
        const Polynomial& factor = named(document, record.polynomial);
        if ((record.multiplicity & 1) == 0) continue;
        if (factor.total_degree() == 1) {
            const Rational aM = factor.coefficient(1, 0);
            const Rational bQ = factor.coefficient(0, 1);
            const Rational c0 = factor.coefficient(0, 0);
            const Rational first_corner =
                aM*Rational(221) + bQ*Rational(3) + c0;
            const Rational second_corner =
                aM*Rational(221) + bQ*Rational(221)*tmax + c0;
            const Rational second_slope = aM + bQ*tmax;
            if (aM.sign() >= 0 && second_slope.sign() >= 0
                    && first_corner.sign() > 0 && second_corner.sign() > 0) {
                continue;
            }
            if (aM.sign() <= 0 && second_slope.sign() <= 0
                    && first_corner.sign() < 0 && second_corner.sign() < 0) {
                overall_sign = -overall_sign;
                continue;
            }
            return {false, 0};
        }
        auto certificate = positive_core_factor(factor, tmax);
        if (!certificate.first) {
            certificate = positive_core_factor(-factor, tmax);
            if (!certificate.first) return {false, 0};
            overall_sign = -overall_sign;
        }
        maximum_M0 = std::max(maximum_M0, certificate.second);
    }
    return {overall_sign > 0, maximum_M0};
}

static Rational resultant_at(const Polynomial& first,
                             const Polynomial& second,
                             const Rational& M_value) {
    const int first_degree = first.degree(1);
    const int second_degree = second.degree(1);
    if (first_degree < 0 || second_degree < 0)
        throw std::runtime_error("resultant of zero polynomial");
    const Univariate f = specialize_first(first, M_value);
    const Univariate g = specialize_first(second, M_value);
    const int size = first_degree + second_degree;
    std::vector<std::vector<Rational>> matrix(
        size, std::vector<Rational>(size, Rational(0)));
    for (int row = 0; row < second_degree; ++row)
        for (int index = 0; index <= first_degree; ++index)
            matrix[row][row + index] = f.value(first_degree - index);
    for (int row = 0; row < first_degree; ++row)
        for (int index = 0; index <= second_degree; ++index)
            matrix[second_degree + row][row + index] =
                g.value(second_degree - index);
    return determinant(std::move(matrix));
}

static bool no_roots_mod_prime(const Univariate& polynomial, int prime) {
    if (prime <= 1 || polynomial.degree() < 2) return false;
    for (int divisor = 2; divisor*divisor <= prime; ++divisor)
        if (prime % divisor == 0) return false;
    if (rational_mod(polynomial.leading(), prime) == 0) return false;
    for (int residue = 0; residue < prime; ++residue) {
        long long value = 0;
        for (int index = polynomial.degree(); index >= 0; --index) {
            value = (value*residue
                     + rational_mod(polynomial.value(index), prime)) % prime;
        }
        if (value == 0) return false;
    }
    return true;
}

static void self_test_exact_arithmetic(CheckState& state) {
    std::cout << "== independent exact-arithmetic self-tests ==\n";
    state.require(Rational(1, 6) + Rational(1, 3) == Rational(1, 2),
                  "rational normalization/arithmetic");
    state.require(integer_sqrt(0) == 0 && integer_sqrt(15) == 3
                      && integer_sqrt(16) == 4
                      && integer_sqrt(9223372036854775807LL)
                         == 3037000499LL,
                  "overflow-safe exact integer square root");
    const Polynomial z = Polynomial::variable(1, 0);
    const Polynomial one = Polynomial::constant(1, Rational(1));
    const Polynomial root_poly =
        (z - Polynomial::constant(1, Rational(2)))
       *(z + Polynomial::constant(1, Rational(3)))
       *(pow_poly(z, 2) + one);
    state.require(roots_on_positive_ray(as_univariate(root_poly), Rational(0)) == 1,
                  "Sturm sequence has the known positive root set");
    state.require(positive_on_ray(as_univariate(pow_poly(z, 2) + one),
                                  Rational(0)),
                  "Sturm positivity for z^2+1");
    const Univariate gcd = monic_gcd(
        as_univariate((z - Polynomial::constant(1, Rational(2)))
                     *(z + Polynomial::constant(1, Rational(1)))),
        as_univariate((z - Polynomial::constant(1, Rational(2)))
                     *(pow_poly(z, 2) + one)));
    state.require(gcd.degree() == 1
                  && gcd.value(0) == Rational(-2)
                  && gcd.value(1) == Rational(1),
                  "Euclidean polynomial gcd");
    state.require(no_roots_mod_prime(as_univariate(pow_poly(z, 2) + one), 3),
                  "modular no-root witness for z^2+1 mod 3");

    const Polynomial M = Polynomial::variable(2, 0);
    const Polynomial q = Polynomial::variable(2, 1);
    const Polynomial f = pow_poly(q, 2) + M;
    const Polynomial g = q - Polynomial::constant(2, Rational(1));
    state.require(resultant_at(f, g, Rational(7)) == Rational(8),
                  "Sylvester determinant Res(q^2+M,q-1)=M+1");
}

static bool specialized_pair_has_no_sector_zero(const Polynomial& first,
                                                const Polynomial& second,
                                                const cpp_int& M_integer,
                                                int sector_divisor) {
    const Rational M_value(M_integer);
    Univariate gcd = monic_gcd(specialize_first(first, M_value),
                               specialize_first(second, M_value));
    if (gcd.is_zero()) return false;
    if (gcd.degree() == 0) return true;
    for (int candidate = 2; candidate < 10000; ++candidate) {
        bool prime = true;
        for (int divisor = 2; divisor*divisor <= candidate; ++divisor)
            if (candidate % divisor == 0) { prime = false; break; }
        if (!prime) continue;
        bool denominator_ok = true;
        for (const Rational& coefficient : gcd.coefficient)
            if (mod_cpp_int(coefficient.denominator, candidate) == 0) {
                denominator_ok = false;
                break;
            }
        if (denominator_ok && no_roots_mod_prime(gcd, candidate)) return true;
    }
    if (M_integer < 0 || M_integer > 24000000)
        return false;  // no finite enumeration certificate was obtained
    const long long M = M_integer.convert_to<long long>();
    for (long long Q = 3; Q*sector_divisor <= M; ++Q)
        if (gcd.evaluate(Rational(Q)).is_zero()) return false;
    return true;
}

static bool check_one_resultant(
        const Document& document, const ResultantRecord& record,
        const Rational& factor_constant,
        const std::vector<FactorRecord>& factors,
        std::string& error) {
    const Polynomial& first = named(document, record.first);
    const Polynomial& second = named(document, record.second);
    const Polynomial& resultant = named(document, record.resultant);
    Polynomial product = Polynomial::constant(1, factor_constant);
    std::vector<cpp_int> integer_roots;
    for (const FactorRecord& factor_record : factors) {
        const Polynomial& factor = named(document, factor_record.polynomial);
        product = product*pow_poly(factor, factor_record.multiplicity);
        const Univariate univariate = as_univariate(factor);
        if (univariate.degree() == 1) {
            const Rational root = -univariate.value(0)/univariate.value(1);
            if (root.denominator == 1) integer_roots.push_back(root.numerator);
        } else if (univariate.degree() >= 2) {
            if (!no_roots_mod_prime(univariate,
                                    factor_record.no_root_prime)) {
                error = "bad modular no-root witness in " + record.label;
                return false;
            }
        }
    }
    if (product != resultant) {
        error = "factor product differs from resultant in " + record.label;
        return false;
    }

    const int degree_bound = first.degree(1)*second.degree(0)
                           + second.degree(1)*first.degree(0);
    if (resultant.arity != 1 || resultant.degree(0) > degree_bound) {
        error = "resultant exceeds the interpolation degree bound in "
              + record.label;
        return false;
    }
    for (int value = 0; value <= degree_bound; ++value) {
        const Rational point(value);
        if (resultant_at(first, second, point)
                != resultant.evaluate({point})) {
            error = "Sylvester determinant differs in " + record.label
                  + " at M=" + std::to_string(value);
            return false;
        }
    }
    std::sort(integer_roots.begin(), integer_roots.end());
    integer_roots.erase(std::unique(integer_roots.begin(), integer_roots.end()),
                        integer_roots.end());
    for (const cpp_int& root : integer_roots) {
        if (root <= record.threshold) continue;
        if (!specialized_pair_has_no_sector_zero(
                first, second, root, record.sector_divisor)) {
            error = "unresolved specialized common zero in " + record.label;
            return false;
        }
    }
    return true;
}

static void check_finite_offsets(const Document& document, CheckState& state) {
    std::cout << "== independent finite-offset witnesses ==\n";
    std::vector<FiniteCaseRecord> cases;
    std::vector<ResultantRecord> resultants;
    std::map<std::string, Rational> G_constant, resultant_constant;
    std::map<std::string, std::vector<FactorRecord>> G_factors, resultant_factors;
    std::vector<Metadata> thresholds;

    for (const Metadata& metadata : document.metadata) {
        const auto& f = metadata.field;
        if (metadata.kind == "FINITE_CASE") {
            if (f.size() != 17) throw std::runtime_error("malformed FINITE_CASE");
            FiniteCaseRecord item;
            item.label = f[0];
            item.u = parse_int(f[1]);
            item.epsilon = parse_int(f[2]);
            item.version = parse_int(f[3]);
            item.G = f[4]; item.lambda = f[5]; item.mu = f[6];
            item.A = f[7]; item.B = f[8]; item.C = f[9];
            item.reduced_G = f[10]; item.reduced_lambda = f[11];
            item.reduced_mu = f[12]; item.common = f[13];
            item.tmax = Rational(parse_integer(f[14]), parse_integer(f[15]));
            item.expected_M0 = parse_int(f[16]);
            cases.push_back(std::move(item));
        } else if (metadata.kind == "FINITE_G_CONST") {
            if (f.size() != 3) throw std::runtime_error("malformed FINITE_G_CONST");
            G_constant[f[0]] = Rational(parse_integer(f[1]), parse_integer(f[2]));
        } else if (metadata.kind == "FINITE_G_FACTOR") {
            if (f.size() != 4) throw std::runtime_error("malformed FINITE_G_FACTOR");
            G_factors[f[0]].push_back({f[1], parse_int(f[2]), parse_int(f[3])});
        } else if (metadata.kind == "RESULTANT") {
            if (f.size() != 6) throw std::runtime_error("malformed RESULTANT");
            resultants.push_back({f[0], f[1], f[2], f[3],
                                  parse_int(f[4]), parse_int(f[5])});
        } else if (metadata.kind == "RESULTANT_CONST") {
            if (f.size() != 3) throw std::runtime_error("malformed RESULTANT_CONST");
            resultant_constant[f[0]] =
                Rational(parse_integer(f[1]), parse_integer(f[2]));
        } else if (metadata.kind == "RESULTANT_FACTOR") {
            if (f.size() != 4) throw std::runtime_error("malformed RESULTANT_FACTOR");
            resultant_factors[f[0]].push_back(
                {f[1], parse_int(f[2]), parse_int(f[3])});
        } else if (metadata.kind == "THRESHOLD") {
            thresholds.push_back(metadata);
        }
    }
    std::set<std::tuple<int, int, int>> finite_case_keys;
    std::set<std::string> finite_case_labels;
    std::map<std::tuple<int, int, int>, const FiniteCaseRecord*> case_by_key;
    int completed_finite_cases = 0;
    for (const FiniteCaseRecord& item : cases) {
        const auto key = std::make_tuple(item.u, item.epsilon, item.version);
        finite_case_keys.insert(key);
        finite_case_labels.insert(item.label);
        case_by_key[key] = &item;
    }
    bool complete_finite_range = cases.size() == 44
        && finite_case_keys.size() == 44 && finite_case_labels.size() == 44;
    for (int offset = 4; offset <= 14; ++offset) {
        for (int epsilon : {-1, 1}) {
            for (int version : {1, 2}) {
                const auto key = std::make_tuple(offset, epsilon, version);
                complete_finite_range = complete_finite_range
                    && finite_case_keys.count(key) == 1;
                if (finite_case_keys.count(key) == 1) {
                    const std::string expected_label =
                        "finite_u" + std::to_string(offset)
                        + "_e" + (epsilon == 1 ? "p" : "m")
                        + "_v" + std::to_string(version);
                    complete_finite_range = complete_finite_range
                        && case_by_key.at(key)->label == expected_label
                        && case_by_key.at(key)->tmax
                           == Rational(1, (offset + 1)*(offset + 1));
                }
            }
        }
    }
    std::set<std::string> resultant_labels;
    std::map<std::string, const ResultantRecord*> resultant_by_label;
    bool canonical_resultant_sectors = true;
    for (const ResultantRecord& record : resultants) {
        resultant_labels.insert(record.label);
        resultant_by_label[record.label] = &record;
        canonical_resultant_sectors = canonical_resultant_sectors
            && record.threshold == 1145 && record.sector_divisor == 24;
    }
    bool complete_resultants = resultants.size() == 66
        && resultant_labels.size() == 66 && canonical_resultant_sectors;
    for (int offset = 4; offset <= 14; ++offset) {
        for (const std::string& parity : {std::string("p"), std::string("m")}) {
            const std::string base = "finite_u" + std::to_string(offset)
                                   + "_e" + parity;
            complete_resultants = complete_resultants
                && resultant_labels.count(base + "_v1_reduced_pair") == 1
                && resultant_labels.count(base + "_v2_reduced_pair") == 1
                && resultant_labels.count(base + "_v2_common_factors") == 1;
        }
    }
    state.require(complete_finite_range,
                  "finite witness contains all 44 offset/parity/pinning cases");
    state.require(complete_resultants,
                  "finite witness contains all 66 nondegeneracy resultants");
    if (!complete_finite_range || !complete_resultants) return;
    for (const FiniteCaseRecord& item : cases) {
        const int failures_before_case = state.failures;
        const Polynomial& G = named(document, item.G);
        const Polynomial& lambda = named(document, item.lambda);
        const Polynomial& mu = named(document, item.mu);
        const Polynomial& A = named(document, item.A);
        const Polynomial& B = named(document, item.B);
        const Polynomial& C = named(document, item.C);
        const Polynomial& reduced_G = named(document, item.reduced_G);
        const Polynomial& reduced_lambda = named(document, item.reduced_lambda);
        const Polynomial& reduced_mu = named(document, item.reduced_mu);
        const Polynomial& common = named(document, item.common);
        const ReconstructedFiniteCase reconstructed =
            reconstruct_finite_case(item.u, item.epsilon, item.version);
        state.require(lambda == reconstructed.lambda
                      && mu == reconstructed.mu
                      && A == reconstructed.A
                      && B == reconstructed.B
                      && C == reconstructed.C,
                      item.label + " independent recurrence reconstruction");
        state.require(G == A*pow_poly(mu, 2) - B*lambda*mu
                           + C*pow_poly(lambda, 2),
                      item.label + " quadratic-form identity");
        state.require(lambda == common*reduced_lambda
                      && mu == common*reduced_mu
                      && G == pow_poly(common, 2)*reduced_G,
                      item.label + " common-factor division identities");
        const ResultantRecord& reduced_pair =
            *resultant_by_label.at(item.label + "_reduced_pair");
        state.require(named(document, reduced_pair.first) == reduced_lambda
                      && named(document, reduced_pair.second) == reduced_mu,
                      item.label + " resultant/reduced-pair linkage");
        if (item.version == 2) {
            const FiniteCaseRecord& primary = *case_by_key.at(
                std::make_tuple(item.u, item.epsilon, 1));
            const ResultantRecord& common_pair =
                *resultant_by_label.at(item.label + "_common_factors");
            state.require(named(document, common_pair.first)
                              == named(document, primary.common)
                          && named(document, common_pair.second) == common,
                          item.label + " resultant/common-factor linkage");
        }
        auto constant = G_constant.find(item.label);
        if (constant == G_constant.end())
            throw std::runtime_error("missing finite G constant");
        Polynomial factor_product = Polynomial::constant(2, constant->second);
        for (const FactorRecord& factor : G_factors[item.label])
            factor_product = factor_product
                           * pow_poly(named(document, factor.polynomial),
                                      factor.multiplicity);
        state.require(factor_product == reduced_G,
                      item.label + " reduced-G factorization");
        const auto positivity = finite_positive_factorization(
            document, constant->second, G_factors[item.label], item.tmax);
        state.require(positivity.first
                      && positivity.second == item.expected_M0,
                      item.label + " independent sector positivity");
        if (state.failures != failures_before_case) return;
        ++completed_finite_cases;
        std::cerr << "  [progress] completed finite cases: "
                  << completed_finite_cases << "/" << cases.size()
                  << "; case=" << item.label << "\n";
        std::cerr.flush();
    }

    // A cheap full factor/modular pass precedes the Sylvester determinants.
    // Besides giving a separate acceptance predicate, this makes a corrupted
    // resultant fail before the expensive parallel replay begins.
    for (const ResultantRecord& record : resultants) {
        auto constant = resultant_constant.find(record.label);
        if (constant == resultant_constant.end())
            throw std::runtime_error("missing resultant constant");
        Polynomial product = Polynomial::constant(1, constant->second);
        bool modular_ok = true;
        for (const FactorRecord& factor_record : resultant_factors.at(record.label)) {
            const Polynomial& factor = named(document, factor_record.polynomial);
            product = product*pow_poly(factor, factor_record.multiplicity);
            const Univariate univariate = as_univariate(factor);
            if (univariate.degree() >= 2)
                modular_ok = modular_ok && no_roots_mod_prime(
                    univariate, factor_record.no_root_prime);
        }
        state.require(product == named(document, record.resultant) && modular_ok,
                      record.label + " factor/modular precheck");
        if (state.failures != 0) return;
    }

    std::vector<int> resultant_ok(resultants.size(), 0);
    std::vector<std::string> resultant_error(resultants.size());
    std::atomic<int> completed_resultants{0};
#pragma omp parallel for schedule(dynamic, 1)
    for (int index = 0; index < static_cast<int>(resultants.size()); ++index) {
        const ResultantRecord& record = resultants[index];
        auto constant = resultant_constant.find(record.label);
        if (constant == resultant_constant.end()) {
            resultant_error[index] = "missing resultant constant";
        } else {
            resultant_ok[index] = check_one_resultant(
                document, record, constant->second,
                resultant_factors.at(record.label), resultant_error[index]);
        }
        const int done = completed_resultants.fetch_add(1) + 1;
#pragma omp critical(independent_checker_progress)
        {
            std::cerr << "  [progress] completed resultants: " << done << "/"
                      << resultants.size() << "; label=" << record.label << "\n";
            std::cerr.flush();
        }
    }
    for (int index = 0; index < static_cast<int>(resultants.size()); ++index)
        state.require(resultant_ok[index] != 0,
                      resultant_error[index].empty()
                        ? resultants[index].label + " exact resultant"
                        : resultant_error[index]);
    state.require(!resultants.empty(), "finite-offset resultants are present");

    state.require(thresholds.size() == 1,
                  "finite witness contains one threshold census");
    if (thresholds.size() == 1) {
        const auto& f = thresholds.front().field;
        if (f.size() != 5) throw std::runtime_error("malformed THRESHOLD");
        state.require(parse_int(f[0]) == 3 && parse_int(f[1]) == 14
                      && parse_int(f[2]) == 4587
                      && parse_int(f[3]) == 3 && parse_int(f[4]) == 15,
                      "finite canonical threshold declaration");
        const std::array<int, 3> found = first_open_gap_cpp(
            parse_int(f[0]), parse_int(f[1]), parse_int(f[2]));
        state.require(found == std::array<int, 3>{{
                          parse_int(f[2]), parse_int(f[3]), parse_int(f[4])}},
                      "finite first-open-gap census");
    }
    if (state.failures == 0)
        std::cout << "  [PASS] " << cases.size() << " finite cases and "
                  << resultants.size() << " resultants\n";
}

static void apply_mutation(std::vector<Document>& documents,
                           const std::string& mutation) {
    if (mutation == "none") return;
    for (Document& document : documents) {
        if (mutation == "odd-sign" && document.suite == "odd-minimum") {
            named(document, "odd_region_O1") = -named(document, "odd_region_O1");
            return;
        }
        if (mutation == "fixed-content"
                && document.suite == "fixed-argument") {
            Polynomial& S = named(document, "fixed_Q3_S");
            S.add_term(Monomial{}, Rational(1));
            return;
        }
        if (mutation == "fixed-ratio"
                && document.suite == "fixed-argument") {
            Polynomial& numerator = named(
                document, "fixed_Q3_ratio_p0_num");
            numerator.add_term(Monomial{}, Rational(1));
            return;
        }
        if (mutation == "finite-recurrence"
                && document.suite == "finite-offset") {
            Polynomial& lambda = named(document, "finite_u4_ep_v1_lam");
            lambda.add_term(Monomial{}, Rational(1));
            return;
        }
        if (mutation == "finite-factor"
                && document.suite == "finite-offset") {
            Polynomial& factor = named(document, "finite_u4_ep_v1_factor_0");
            factor.add_term(Monomial{}, Rational(1));
            return;
        }
        if (mutation == "resultant"
                && document.suite == "finite-offset") {
            Polynomial& resultant = named(
                document, "finite_u4_ep_v1_reduced_pair_R");
            resultant.add_term(Monomial{}, Rational(1));
            return;
        }
        if (mutation == "resultant-link"
                && document.suite == "finite-offset") {
            for (Metadata& metadata : document.metadata) {
                if (metadata.kind == "RESULTANT"
                        && !metadata.field.empty()
                        && metadata.field[0]
                           == "finite_u4_ep_v1_reduced_pair") {
                    metadata.field[1] = "finite_u4_ep_v1_G";
                    return;
                }
            }
        }
    }
    throw std::runtime_error("mutation target unavailable: " + mutation);
}

int main(int argc, char** argv) {
    try {
        std::vector<std::string> paths;
        std::string mutation = "none";
        for (int index = 1; index < argc; ++index) {
            const std::string argument = argv[index];
            const std::string prefix = "--mutation=";
            if (argument.rfind(prefix, 0) == 0)
                mutation = argument.substr(prefix.size());
            else
                paths.push_back(argument);
        }
        if (paths.empty()) {
            std::cerr << "usage: " << argv[0]
                      << " WITNESS... [--mutation=NAME]\n";
            return 6;
        }

        std::vector<Document> documents;
        for (const std::string& path : paths) documents.push_back(read_document(path));
        apply_mutation(documents, mutation);

        CheckState state;
        self_test_exact_arithmetic(state);
        for (const Document& document : documents) {
            if (document.suite == "odd-minimum")
                check_odd_minimum(document, state);
            else if (document.suite == "fixed-argument")
                check_fixed_argument(document, state);
            else if (document.suite == "finite-offset")
                check_finite_offsets(document, state);
            else
                throw std::runtime_error("unsupported witness suite: " + document.suite);
        }
        std::cout << "independent certificate checks: " << state.checks
                  << "; failures: " << state.failures << "\n";
        if (state.failures == 0) {
            std::cout << "INDEPENDENT CERTIFICATE PASS\n";
            return 0;
        }
        return 1;
    } catch (const std::exception& error) {
        std::cerr << "independent checker error: " << error.what() << "\n";
        return 2;
    }
}
