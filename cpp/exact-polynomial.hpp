#ifndef KRAW_EXACT_POLYNOMIAL_HPP
#define KRAW_EXACT_POLYNOMIAL_HPP

#include <boost/multiprecision/cpp_int.hpp>

#include <algorithm>
#include <array>
#include <map>
#include <stdexcept>
#include <utility>
#include <vector>

namespace kraw_exact {

using boost::multiprecision::cpp_int;

inline cpp_int abs_int(cpp_int value) {
    return value < 0 ? -value : value;
}

inline cpp_int gcd_int(cpp_int left, cpp_int right) {
    left = abs_int(left);
    right = abs_int(right);
    while (right != 0) {
        cpp_int remainder = left % right;
        left = right;
        right = remainder;
    }
    return left;
}

struct Rational {
    cpp_int numerator{0};
    cpp_int denominator{1};

    Rational() = default;
    Rational(long long value) : numerator(value), denominator(1) {}
    Rational(cpp_int value) : numerator(std::move(value)), denominator(1) {}
    Rational(cpp_int n, cpp_int d)
        : numerator(std::move(n)), denominator(std::move(d)) {
        normalize();
    }

    void normalize() {
        if (denominator == 0) throw std::runtime_error("zero denominator");
        if (denominator < 0) {
            numerator = -numerator;
            denominator = -denominator;
        }
        if (numerator == 0) {
            denominator = 1;
            return;
        }
        const cpp_int divisor = gcd_int(numerator, denominator);
        numerator /= divisor;
        denominator /= divisor;
    }

    int sign() const { return (numerator > 0) - (numerator < 0); }
    bool is_zero() const { return numerator == 0; }
};

inline Rational operator+(const Rational& a, const Rational& b) {
    return Rational(a.numerator*b.denominator + b.numerator*a.denominator,
                    a.denominator*b.denominator);
}
inline Rational operator-(const Rational& a, const Rational& b) {
    return Rational(a.numerator*b.denominator - b.numerator*a.denominator,
                    a.denominator*b.denominator);
}
inline Rational operator-(const Rational& a) {
    return Rational(-a.numerator, a.denominator);
}
inline Rational operator*(const Rational& a, const Rational& b) {
    if (a.is_zero() || b.is_zero()) return Rational(0);
    // Cross-cancellation keeps intermediate determinants and grid checks
    // substantially smaller.
    const cpp_int g1 = gcd_int(a.numerator, b.denominator);
    const cpp_int g2 = gcd_int(b.numerator, a.denominator);
    return Rational((a.numerator/g1)*(b.numerator/g2),
                    (a.denominator/g2)*(b.denominator/g1));
}
inline Rational operator/(const Rational& a, const Rational& b) {
    if (b.is_zero()) throw std::runtime_error("division by zero rational");
    return a * Rational(b.denominator, b.numerator);
}
inline bool operator==(const Rational& a, const Rational& b) {
    return a.numerator == b.numerator && a.denominator == b.denominator;
}
inline bool operator!=(const Rational& a, const Rational& b) {
    return !(a == b);
}
inline bool operator<(const Rational& a, const Rational& b) {
    return a.numerator*b.denominator < b.numerator*a.denominator;
}
inline bool operator>(const Rational& a, const Rational& b) { return b < a; }
inline bool operator<=(const Rational& a, const Rational& b) {
    return !(b < a);
}
inline bool operator>=(const Rational& a, const Rational& b) {
    return !(a < b);
}

inline Rational abs_rat(const Rational& value) {
    return value.sign() < 0 ? -value : value;
}

inline Rational pow_rat(Rational base, int exponent) {
    if (exponent < 0) throw std::runtime_error("negative rational exponent");
    Rational result(1);
    while (exponent > 0) {
        if (exponent & 1) result = result*base;
        exponent >>= 1;
        if (exponent) base = base*base;
    }
    return result;
}

struct Monomial {
    std::array<int, 2> exponent{{0, 0}};
    bool operator<(const Monomial& other) const {
        return exponent < other.exponent;
    }
    bool operator==(const Monomial& other) const {
        return exponent == other.exponent;
    }
};

struct Polynomial {
    int arity{1};
    std::map<Monomial, Rational> terms;

    explicit Polynomial(int variables = 1) : arity(variables) {
        if (arity < 1 || arity > 2)
            throw std::runtime_error("only one- and two-variable polynomials are supported");
    }

    static Polynomial constant(int arity, const Rational& value) {
        Polynomial out(arity);
        out.add_term({{0, 0}}, value);
        return out;
    }

    static Polynomial variable(int arity, int index) {
        if (index < 0 || index >= arity)
            throw std::runtime_error("polynomial variable out of range");
        Polynomial out(arity);
        Monomial monomial;
        monomial.exponent[index] = 1;
        out.add_term(monomial, Rational(1));
        return out;
    }

    void add_term(const Monomial& monomial, const Rational& coefficient) {
        if (coefficient.is_zero()) return;
        Rational& slot = terms[monomial];
        slot = slot + coefficient;
        if (slot.is_zero()) terms.erase(monomial);
    }

    bool is_zero() const { return terms.empty(); }

    int degree(int variable) const {
        if (variable < 0 || variable >= arity)
            throw std::runtime_error("polynomial degree variable out of range");
        int result = -1;
        for (const auto& item : terms)
            result = std::max(result, item.first.exponent[variable]);
        return result;
    }

    int total_degree() const {
        int result = -1;
        for (const auto& item : terms)
            result = std::max(result,
                item.first.exponent[0] + item.first.exponent[1]);
        return result;
    }

    Rational coefficient(int first, int second = 0) const {
        Monomial monomial;
        monomial.exponent = {{first, second}};
        const auto found = terms.find(monomial);
        return found == terms.end() ? Rational(0) : found->second;
    }

    Rational evaluate(const std::vector<Rational>& values) const {
        if (static_cast<int>(values.size()) != arity)
            throw std::runtime_error("polynomial evaluation arity mismatch");
        Rational result(0);
        for (const auto& item : terms) {
            Rational term = item.second;
            for (int variable = 0; variable < arity; ++variable)
                term = term*pow_rat(values[variable],
                                    item.first.exponent[variable]);
            result = result + term;
        }
        return result;
    }
};

inline void require_same_arity(const Polynomial& a, const Polynomial& b) {
    if (a.arity != b.arity)
        throw std::runtime_error("polynomial arity mismatch");
}

inline Polynomial operator+(const Polynomial& a, const Polynomial& b) {
    require_same_arity(a, b);
    Polynomial result = a;
    for (const auto& item : b.terms) result.add_term(item.first, item.second);
    return result;
}
inline Polynomial operator-(const Polynomial& a, const Polynomial& b) {
    require_same_arity(a, b);
    Polynomial result = a;
    for (const auto& item : b.terms) result.add_term(item.first, -item.second);
    return result;
}
inline Polynomial operator-(const Polynomial& a) {
    Polynomial result(a.arity);
    for (const auto& item : a.terms) result.add_term(item.first, -item.second);
    return result;
}
inline Polynomial operator*(const Polynomial& a, const Polynomial& b) {
    require_same_arity(a, b);
    Polynomial result(a.arity);
    for (const auto& left : a.terms) {
        for (const auto& right : b.terms) {
            Monomial monomial;
            monomial.exponent = {{
                left.first.exponent[0] + right.first.exponent[0],
                left.first.exponent[1] + right.first.exponent[1]
            }};
            result.add_term(monomial, left.second*right.second);
        }
    }
    return result;
}
inline Polynomial operator*(const Polynomial& a, const Rational& scalar) {
    Polynomial result(a.arity);
    for (const auto& item : a.terms)
        result.add_term(item.first, item.second*scalar);
    return result;
}
inline Polynomial operator*(const Rational& scalar, const Polynomial& a) {
    return a*scalar;
}
inline Polynomial operator/(const Polynomial& a, const Rational& scalar) {
    return a*(Rational(1)/scalar);
}
inline bool operator==(const Polynomial& a, const Polynomial& b) {
    return a.arity == b.arity && a.terms == b.terms;
}
inline bool operator!=(const Polynomial& a, const Polynomial& b) {
    return !(a == b);
}

inline Polynomial pow_poly(Polynomial base, int exponent) {
    if (exponent < 0) throw std::runtime_error("negative polynomial exponent");
    Polynomial result = Polynomial::constant(base.arity, Rational(1));
    while (exponent > 0) {
        if (exponent & 1) result = result*base;
        exponent >>= 1;
        if (exponent) base = base*base;
    }
    return result;
}

inline Polynomial substitute(const Polynomial& source,
                             const std::vector<Polynomial>& images) {
    if (static_cast<int>(images.size()) != source.arity)
        throw std::runtime_error("polynomial substitution arity mismatch");
    const int target_arity = images.front().arity;
    for (const Polynomial& image : images)
        if (image.arity != target_arity)
            throw std::runtime_error("substitution target arity mismatch");
    Polynomial result(target_arity);
    for (const auto& item : source.terms) {
        Polynomial term = Polynomial::constant(target_arity, item.second);
        for (int variable = 0; variable < source.arity; ++variable)
            term = term*pow_poly(images[variable],
                                 item.first.exponent[variable]);
        result = result + term;
    }
    return result;
}

class Univariate {
public:
    std::vector<Rational> coefficient;  // low degree first

    Univariate() = default;
    explicit Univariate(std::vector<Rational> values)
        : coefficient(std::move(values)) { trim(); }

    void trim() {
        while (!coefficient.empty() && coefficient.back().is_zero())
            coefficient.pop_back();
    }
    bool is_zero() const { return coefficient.empty(); }
    int degree() const { return static_cast<int>(coefficient.size()) - 1; }
    Rational leading() const {
        return is_zero() ? Rational(0) : coefficient.back();
    }
    Rational value(int index) const {
        return index < 0 || index > degree() ? Rational(0)
                                             : coefficient[index];
    }
    Rational evaluate(const Rational& x) const {
        Rational result(0);
        for (int index = degree(); index >= 0; --index)
            result = result*x + coefficient[index];
        return result;
    }
    Univariate derivative() const {
        if (degree() <= 0) return Univariate();
        std::vector<Rational> result(degree());
        for (int index = 1; index <= degree(); ++index)
            result[index - 1] = coefficient[index]*Rational(index);
        return Univariate(std::move(result));
    }
};

inline Univariate operator-(const Univariate& value) {
    std::vector<Rational> result = value.coefficient;
    for (Rational& coefficient : result) coefficient = -coefficient;
    return Univariate(std::move(result));
}

inline std::pair<Univariate, Univariate> divide_with_remainder(
        Univariate dividend, const Univariate& divisor) {
    if (divisor.is_zero()) throw std::runtime_error("polynomial division by zero");
    std::vector<Rational> quotient(
        std::max(0, dividend.degree() - divisor.degree() + 1), Rational(0));
    while (!dividend.is_zero() && dividend.degree() >= divisor.degree()) {
        const int shift = dividend.degree() - divisor.degree();
        const Rational scale = dividend.leading()/divisor.leading();
        quotient[shift] = quotient[shift] + scale;
        for (int index = 0; index <= divisor.degree(); ++index)
            dividend.coefficient[index + shift] =
                dividend.coefficient[index + shift] - divisor.coefficient[index]*scale;
        dividend.trim();
    }
    return {Univariate(std::move(quotient)), dividend};
}

inline Univariate monic_gcd(Univariate left, Univariate right) {
    while (!right.is_zero()) {
        Univariate remainder = divide_with_remainder(left, right).second;
        left = std::move(right);
        right = std::move(remainder);
    }
    if (left.is_zero()) return left;
    const Rational leading = left.leading();
    for (Rational& coefficient : left.coefficient)
        coefficient = coefficient/leading;
    return left;
}

inline Univariate as_univariate(const Polynomial& polynomial) {
    if (polynomial.arity != 1)
        throw std::runtime_error("expected a univariate polynomial");
    std::vector<Rational> coefficients(polynomial.degree(0) + 1, Rational(0));
    for (const auto& item : polynomial.terms)
        coefficients[item.first.exponent[0]] = item.second;
    return Univariate(std::move(coefficients));
}

inline Polynomial coefficient_in_second(const Polynomial& polynomial,
                                        int exponent) {
    if (polynomial.arity != 2)
        throw std::runtime_error("expected a bivariate polynomial");
    Polynomial result(1);
    for (const auto& item : polynomial.terms) {
        if (item.first.exponent[1] != exponent) continue;
        Monomial monomial;
        monomial.exponent[0] = item.first.exponent[0];
        result.add_term(monomial, item.second);
    }
    return result;
}

inline Univariate specialize_first(const Polynomial& polynomial,
                                   const Rational& first) {
    if (polynomial.arity != 2)
        throw std::runtime_error("expected a bivariate polynomial");
    std::vector<Rational> coefficients(polynomial.degree(1) + 1, Rational(0));
    for (const auto& item : polynomial.terms) {
        coefficients[item.first.exponent[1]] =
            coefficients[item.first.exponent[1]]
            + item.second*pow_rat(first, item.first.exponent[0]);
    }
    return Univariate(std::move(coefficients));
}

inline std::vector<Univariate> sturm_sequence(const Univariate& polynomial) {
    if (polynomial.is_zero())
        throw std::runtime_error("Sturm sequence of zero polynomial");
    std::vector<Univariate> sequence;
    sequence.push_back(polynomial);
    Univariate derivative = polynomial.derivative();
    if (derivative.is_zero()) return sequence;
    sequence.push_back(std::move(derivative));
    while (!sequence.back().is_zero()) {
        const std::size_t size = sequence.size();
        Univariate remainder = divide_with_remainder(
            sequence[size - 2], sequence[size - 1]).second;
        if (remainder.is_zero()) break;
        sequence.push_back(-remainder);
    }
    return sequence;
}

inline int variations_at(const std::vector<Univariate>& sequence,
                         const Rational& point) {
    int previous = 0;
    int variations = 0;
    for (const Univariate& polynomial : sequence) {
        const int sign = polynomial.evaluate(point).sign();
        if (sign == 0) continue;
        if (previous != 0 && sign != previous) ++variations;
        previous = sign;
    }
    return variations;
}

inline int variations_at_positive_infinity(
        const std::vector<Univariate>& sequence) {
    int previous = 0;
    int variations = 0;
    for (const Univariate& polynomial : sequence) {
        const int sign = polynomial.leading().sign();
        if (sign == 0) continue;
        if (previous != 0 && sign != previous) ++variations;
        previous = sign;
    }
    return variations;
}

inline int roots_on_positive_ray(const Univariate& polynomial,
                                 const Rational& onset) {
    const std::vector<Univariate> sequence = sturm_sequence(polynomial);
    return variations_at(sequence, onset)
         - variations_at_positive_infinity(sequence);
}

inline bool positive_on_ray(const Univariate& polynomial,
                            const Rational& onset) {
    return !polynomial.is_zero()
        && polynomial.leading().sign() > 0
        && polynomial.evaluate(onset).sign() > 0
        && roots_on_positive_ray(polynomial, onset) == 0;
}

inline Rational determinant(std::vector<std::vector<Rational>> matrix) {
    const int size = static_cast<int>(matrix.size());
    if (size == 0) return Rational(1);
    for (const auto& row : matrix)
        if (static_cast<int>(row.size()) != size)
            throw std::runtime_error("determinant matrix is not square");
    int parity = 1;
    Rational result(1);
    for (int column = 0; column < size; ++column) {
        int pivot = column;
        while (pivot < size && matrix[pivot][column].is_zero()) ++pivot;
        if (pivot == size) return Rational(0);
        if (pivot != column) {
            std::swap(matrix[pivot], matrix[column]);
            parity = -parity;
        }
        const Rational pivot_value = matrix[column][column];
        result = result*pivot_value;
        for (int row = column + 1; row < size; ++row) {
            if (matrix[row][column].is_zero()) continue;
            const Rational factor = matrix[row][column]/pivot_value;
            for (int index = column + 1; index < size; ++index)
                matrix[row][index] = matrix[row][index]
                                   - factor*matrix[column][index];
            matrix[row][column] = Rational(0);
        }
    }
    return parity < 0 ? -result : result;
}

inline long long mod_cpp_int(const cpp_int& value, long long modulus) {
    cpp_int remainder = value % modulus;
    long long result = remainder.convert_to<long long>();
    if (result < 0) result += modulus;
    return result;
}

inline long long modular_inverse(long long value, long long modulus) {
    long long old_r = value, r = modulus;
    long long old_s = 1, s = 0;
    while (r != 0) {
        const long long quotient = old_r/r;
        const long long next_r = old_r - quotient*r;
        old_r = r;
        r = next_r;
        const long long next_s = old_s - quotient*s;
        old_s = s;
        s = next_s;
    }
    if (old_r != 1) throw std::runtime_error("noninvertible modular value");
    old_s %= modulus;
    if (old_s < 0) old_s += modulus;
    return old_s;
}

inline long long rational_mod(const Rational& value, long long modulus) {
    const long long numerator = mod_cpp_int(value.numerator, modulus);
    const long long denominator = mod_cpp_int(value.denominator, modulus);
    if (denominator == 0)
        throw std::runtime_error("rational denominator vanishes modulo prime");
    return numerator*modular_inverse(denominator, modulus) % modulus;
}

}  // namespace kraw_exact

#endif
