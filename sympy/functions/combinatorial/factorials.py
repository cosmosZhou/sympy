from sympy.core import S, sympify, Dummy, Mod
from sympy.core.cache import cacheit
from sympy.core.compatibility import reduce, HAS_GMPY
from sympy.core.function import Function, ArgumentIndexError
from sympy.core.logic import fuzzy_and
from sympy.core.numbers import Integer, pi
from sympy.core.relational import Eq
from sympy.ntheory import sieve
# from sympy.polys.polytools import Poly

from math import sqrt as _sqrt


class CombinatorialFunction(Function):
    """Base class for combinatorial functions. """

    def _eval_shape(self):
        return ()

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.simplify.combsimp import combsimp
        # combinatorial function with non-integer arguments is
        # automatically passed to gammasimp
        expr = combsimp(self)
        if measure(expr) <= ratio * measure(self):
            return expr
        return self

###############################################################################
######################## FACTORIAL and MULTI-FACTORIAL ########################
###############################################################################


class Factorial(CombinatorialFunction):
    r"""Implementation of factorial function over nonnegative integers.
       By convention (consistent with the Gamma function and the binomial
       coefficients), factorial of a negative integer is complex infinity.

       The factorial is very important in combinatorics where it gives
       the number of ways in which `n` objects can be permuted. It also
       arises in calculus, probability, number theory, etc.

       There is strict relation of factorial with Gamma function. In
       fact `n! = Gamma(n+1)` for nonnegative integers. Rewrite of this
       kind is very useful in case of combinatorial simplification.

       Computation of the factorial is done using two algorithms. For
       small arguments a precomputed look up table is used. However for bigger
       input algorithm Prime-Swing is used. It is the fastest algorithm
       known and computes `n!` via prime factorization of special class
       of numbers, called here the 'Swing Numbers'.

       Examples
       ========

       >>> from sympy import Symbol, factorial, S
       >>> n = Symbol('n', integer=True)

       >>> factorial(0)
       1

       >>> factorial(7)
       5040

       >>> factorial(-2)
       zoo

       >>> factorial(n)
       factorial(n)

       >>> factorial(2*n)
       factorial(2*n)

       >>> factorial(S(1)/2)
       factorial(1/2)

       See Also
       ========

       factorial2, RisingFactorial, FallingFactorial
    """

    is_nonzero = True
    
    def fdiff(self, argindex=1):
        from sympy import Gamma, polygamma
        if argindex == 1:
            return Gamma(self.args[0] + 1) * polygamma(0, self.args[0] + 1)
        else:
            raise ArgumentIndexError(self, argindex)

    _small_swing = [
        1, 1, 1, 3, 3, 15, 5, 35, 35, 315, 63, 693, 231, 3003, 429, 6435, 6435, 109395,
        12155, 230945, 46189, 969969, 88179, 2028117, 676039, 16900975, 1300075,
        35102025, 5014575, 145422675, 9694845, 300540195, 300540195
    ]

    _small_factorials = []

    @classmethod
    def _swing(cls, n):
        if n < 33:
            return cls._small_swing[n]
        else:
            N, primes = int(_sqrt(n)), []

            for prime in sieve.primerange(3, N + 1):
                p, q = 1, n

                while True:
                    q //= prime

                    if q > 0:
                        if q & 1 == 1:
                            p *= prime
                    else:
                        break

                if p > 1:
                    primes.append(p)

            for prime in sieve.primerange(N + 1, n // 3 + 1):
                if (n // prime) & 1 == 1:
                    primes.append(prime)

            L_product = R_product = 1

            for prime in sieve.primerange(n // 2 + 1, n + 1):
                L_product *= prime

            for prime in primes:
                R_product *= prime

            return L_product * R_product

    @classmethod
    def _recursive(cls, n):
        if n < 2:
            return 1
        else:
            return (cls._recursive(n // 2) ** 2) * cls._swing(n)

    @classmethod
    def eval(cls, n):
        n = sympify(n)

        if n.is_Number:
            if n is S.Zero:
                return S.One
            elif n is S.Infinity:
                return S.Infinity
            elif n.is_Integer:
                if n.is_negative:
                    return S.ComplexInfinity
                else:
                    n = n.p

                    if n < 20:
                        if not cls._small_factorials:
                            result = 1
                            for i in range(1, 20):
                                result *= i
                                cls._small_factorials.append(result)
                        result = cls._small_factorials[n - 1]

                    # GMPY factorial is faster, use it when available
                    elif HAS_GMPY:
                        from sympy.core.compatibility import gmpy
                        result = gmpy.fac(n)

                    else:
                        bits = bin(n).count('1')
                        result = cls._recursive(n) * 2 ** (n - bits)

                    return Integer(result)

    def _facmod(self, n, q):
        res, N = 1, int(_sqrt(n))

        # Exponent of prime p in n! is e_p(n) = [n/p] + [n/p**2] + ...
        # for p > sqrt(n), e_p(n) < sqrt(n), the primes with [n/p] = m,
        # occur consecutively and are grouped together in pw[m] for
        # simultaneous exponentiation at a later stage
        pw = [1] * N

        m = 2  # to initialize the if condition below
        for prime in sieve.primerange(2, n + 1):
            if m > 1:
                m, y = 0, n // prime
                while y:
                    m += y
                    y //= prime
            if m < N:
                pw[m] = pw[m] * prime % q
            else:
                res = res * pow(prime, m, q) % q

        for ex, bs in enumerate(pw):
            if ex == 0 or bs == 1:
                continue
            if bs == 0:
                return 0
            res = res * pow(bs, ex, q) % q

        return res

    def _eval_Mod(self, q):
        n = self.args[0]
        if n.is_integer and n.is_nonnegative and q.is_integer:
            aq = abs(q)
            d = aq - n
            if d.is_nonpositive:
                return 0
            else:
                isprime = aq.is_prime
                if d == 1:
                    # Apply Wilson's theorem (if a natural number n > 1
                    # is a prime number, then (n-1)! = -1 mod n) and
                    # its inverse (if n > 4 is a composite number, then
                    # (n-1)! = 0 mod n)
                    if isprime:
                        return -1 % q
                    elif isprime is False and (aq - 6).is_nonnegative:
                        return 0
                elif n.is_Integer and q.is_Integer:
                    n, d, aq = map(int, (n, d, aq))
                    if isprime and (d - 1 < n):
                        fc = self._facmod(d - 1, aq)
                        fc = pow(fc, aq - 2, aq)
                        if d % 2:
                            fc = -fc
                    else:
                        fc = self._facmod(n, aq)

                    return Integer(fc % q)

#     def _eval_rewrite_as_gamma(self, n, **kwargs):
#         from sympy import Gamma
#         return Gamma(n + 1)

    def _eval_rewrite_as_Product(self, n, **kwargs):
        from sympy import Product
        if n.is_nonnegative and n.is_integer:
            i = Dummy('i', integer=True)
            return Product(i, (i, 1, n))

    def _eval_is_extended_integer(self):
        arg = self.arg
        if arg.is_extended_integer and arg.is_extended_nonnegative:
            return True

    def _eval_is_extended_positive(self):
        arg = self.arg
        if arg.is_extended_integer and arg.is_extended_nonnegative:
            return True

    def _eval_is_even(self):
        x = self.args[0]
        if x.is_integer and x.is_nonnegative:
            return (x - 2).is_nonnegative

    def _eval_is_composite(self):
        x = self.args[0]
        if x.is_integer and x.is_nonnegative:
            return (x - 3).is_nonnegative

    def _eval_is_extended_real(self):
        x = self.args[0]
        if x.is_extended_nonnegative or x.is_noninteger:
            return True

    def _eval_is_rational(self):
        if self.args[0].is_integer and self.args[0].is_nonnegative:
            return True

    def _sympystr(self, p):
        n = self.arg
        latex = p._print(n)
        return 'Factorial(%s)' % latex

    def _latex(self, p, exp=None):
        from sympy.printing.precedence import PRECEDENCE
        tex = r"%s!" % p.parenthesize(self.args[0], PRECEDENCE["Func"])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex


factorial = Factorial

    
class MultiFactorial(CombinatorialFunction):
    pass


class subfactorial(CombinatorialFunction):
    r"""The subfactorial counts the derangements of $n$ items and is
    defined for non-negative integers as:

    .. math:: !n = \begin{cases} 1 & n = 0 \\ 0 & n = 1 \\
                    (n-1)(!(n-1) + !(n-2)) & n > 1 \end{cases}

    It can also be written as ``int(round(n!/exp(1)))`` but the
    recursive definition with caching is implemented for this function.

    An interesting analytic expression is the following [2]_

    .. math:: !x = \Gamma(x + 1, -1)/e

    which is valid for non-negative integers `x`. The above formula
    is not very useful in case of non-integers. `\Gamma(x + 1, -1)` is
    single-valued only for integral arguments `x`, elsewhere on the positive
    real axis it has an infinite number of branches none of which are real.

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Subfactorial
    .. [2] https://mathworld.wolfram.com/Subfactorial.html

    Examples
    ========

    >>> from sympy import subfactorial
    >>> from sympy.abc import n
    >>> subfactorial(n + 1)
    subfactorial(n + 1)
    >>> subfactorial(5)
    44

    See Also
    ========

    factorial, uppergamma,
    sympy.utilities.iterables.generate_derangements
    """

    @classmethod
    @cacheit
    def _eval(self, n):
        if not n:
            return S.One
        elif n == 1:
            return S.Zero
        return (n - 1) * (self._eval(n - 1) + self._eval(n - 2))

    @classmethod
    def eval(cls, arg):
        if arg.is_Number:
            if arg.is_Integer and arg.is_nonnegative:
                return cls._eval(arg)
            elif arg is S.NaN:
                return S.NaN
            elif arg is S.Infinity:
                return S.Infinity

    def _eval_is_even(self):
        if self.args[0].is_odd and self.args[0].is_nonnegative:
            return True

    def _eval_is_extended_integer(self):
        arg = self.arg
        if arg.is_extended_integer and arg.is_nonnegative:
            return True

    def _eval_rewrite_as_uppergamma(self, arg, **kwargs):
        from sympy import uppergamma
        return uppergamma(arg + 1, -1) / S.Exp1

    def _eval_is_extended_negative(self):
        if self.args[0].is_integer and self.args[0].is_extended_negative:
            return True


class Factorial2(CombinatorialFunction):
    r"""The double factorial `n!!`, not to be confused with `(n!)!`

    The double factorial is defined for nonnegative integers and for odd
    negative integers as:

    .. math:: n!! = \begin{cases} 1 & n = 0 \\
                    n(n-2)(n-4) \cdots 1 & n\ \text{positive odd} \\
                    n(n-2)(n-4) \cdots 2 & n\ \text{positive even} \\
                    (n+2)!!/(n+2) & n\ \text{negative odd} \end{cases}

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Double_factorial

    Examples
    ========

    >>> from sympy import factorial2, var
    >>> n = var('n')
    >>> n
    n
    >>> factorial2(n + 1)
    factorial2(n + 1)
    >>> factorial2(5)
    15
    >>> factorial2(-1)
    1
    >>> factorial2(-5)
    1/3

    See Also
    ========

    factorial, RisingFactorial, FallingFactorial
    """

    @classmethod
    def eval(cls, arg):
        # TODO: extend this to complex numbers?

        if arg.is_Number:
            if not arg.is_Integer:
                raise ValueError("argument must be nonnegative integer "
                                    "or negative odd integer")

            # This implementation is faster than the recursive one
            # It also avoids "maximum recursion depth exceeded" runtime error
            if arg.is_nonnegative:
                if arg.is_even:
                    k = arg / 2
                    return 2 ** k * factorial(k)
                return factorial(arg) / factorial2(arg - 1)

            if arg.is_odd:
                return arg * (S.NegativeOne) ** ((1 - arg) / 2) / factorial2(-arg)
            raise ValueError("argument must be nonnegative integer "
                                "or negative odd integer")

    def _eval_is_even(self):
        # Double factorial is even for every positive even input
        # Double factorial is odd for every odd input not smaller than -3, and
        # for 0
        
        n = self.args[0]
        if n.is_integer:
            if n.is_odd:
                return False
            if n.is_even:
                if n.is_positive:
                    return True
                if n.is_zero:
                    return False

    def _eval_is_extended_integer(self):
        # Double factorial is an integer for every nonnegative input, and for
        # -1 and -3
        n = self.arg
        if n.is_extended_integer:
            if (n + 1).is_extended_nonnegative:
                return True
            if n.is_odd:
                return (n + 3).is_extended_nonnegative

    def _eval_is_extended_positive(self):
        # Double factorial is positive for every nonnegative input, and for
        # every odd negative input which is of the form -1-4k for an
        # nonnegative integer k
        n = self.args[0]
        if n.is_integer:
            if (n + 1).is_extended_nonnegative:
                return True
            if n.is_odd:
                return ((n + 1) / 2).is_even

    def _eval_rewrite_as_gamma(self, n, **kwargs):
        from sympy import Gamma, Piecewise, sqrt
        return 2 ** (n / 2) * Gamma(n / 2 + 1) * Piecewise((1, Eq(Mod(n, 2), 0)),
                (sqrt(2 / pi), Eq(Mod(n, 2), 1)))

    def _sympystr(self, p):
        n = self.arg
        latex = p._print(n)
        return 'Factorial2(%s)' % latex

    def _latex(self, p, exp=None):
        from sympy.printing.precedence import PRECEDENCE
        tex = r"%s!!" % p.parenthesize(self.args[0], PRECEDENCE["Func"])

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex


factorial2 = Factorial2
###############################################################################
######################## RISING and FALLING FACTORIALS ########################
###############################################################################


class RisingFactorial(CombinatorialFunction):
    r"""
    Rising factorial (also called Pochhammer symbol [1]_) is a double valued
    function arising in concrete mathematics, hypergeometric functions
    and series expansions. It is defined by:

    .. math:: \texttt{rf(y, k)} = (x)^k = x \cdot (x+1) \cdots (x+k-1)

    where `x` can be arbitrary expression and `k` is an integer. For
    more information check "Concrete mathematics" by Graham, pp. 66
    or visit https://mathworld.wolfram.com/RisingFactorial.html page.

    When `x` is a `~.Poly` instance of degree $\ge 1$ with a single variable,
    `(x)^k = x(y) \cdot x(y+1) \cdots x(y+k-1)`, where `y` is the
    variable of `x`. This is as described in [2]_.

    Examples
    ========

    >>> from sympy import rf, Poly
    >>> from sympy.abc import x
    >>> rf(x, 0)
    1
    >>> rf(1, 5)
    120
    >>> rf(x, 5) == x*(1 + x)*(2 + x)*(3 + x)*(4 + x)
    True
    >>> rf(Poly(x**3, x), 2)
    Poly(x**6 + 3*x**5 + 3*x**4 + x**3, x, domain='ZZ')

    Rewriting is complicated unless the relationship between
    the arguments is known, but rising factorial can
    be rewritten in terms of Gamma, factorial, binomial,
    and falling factorial.

    >>> from sympy import Symbol, factorial, ff, binomial, Gamma
    >>> n = Symbol('n', integer=True, positive=True)
    >>> R = rf(n, n + 2)
    >>> for i in (rf, ff, factorial, binomial, Gamma):
    ...  R.rewrite(i)
    ...
    RisingFactorial(n, n + 2)
    FallingFactorial(2*n + 1, n + 2)
    factorial(2*n + 1)/factorial(n - 1)
    binomial(2*n + 1, n + 2)*factorial(n + 2)
    Gamma(2*n + 2)/Gamma(n)

    See Also
    ========

    factorial, factorial2, FallingFactorial

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Pochhammer_symbol
    .. [2] Peter Paule, "Greatest Factorial Factorization and Symbolic
           Summation", Journal of Symbolic Computation, vol. 20, pp. 235-268,
           1995.

    """

    @classmethod
    def eval(cls, x, k):
        x = sympify(x)
        k = sympify(k)

        if x is S.NaN or k is S.NaN:
            return S.NaN
        elif x is S.One:
            return factorial(k)
        elif k.is_Integer:
            if k is S.Zero:
                return S.One
            else:
                if k.is_positive:
                    if x is S.Infinity:
                        return S.Infinity
                    elif x is S.NegativeInfinity:
                        if k.is_odd:
                            return S.NegativeInfinity
                        else:
                            return S.Infinity
                    else:
                        if x.is_Poly:
                            gens = x.gens
                            if len(gens) != 1:
                                raise ValueError("rf only defined for "
                                            "polynomials on one generator")
                            else:
                                return reduce(lambda r, i:
                                              r * (x.shift(i).expand()),
                                              range(0, int(k)), 1)
                        else:
                            return reduce(lambda r, i: r * (x + i),
                                        range(0, int(k)), 1)

                else:
                    if x is S.Infinity:
                        return S.Infinity
                    elif x is S.NegativeInfinity:
                        return S.Infinity
                    else:
                        if x.is_Poly:
                            gens = x.gens
                            if len(gens) != 1:
                                raise ValueError("rf only defined for "
                                            "polynomials on one generator")
                            else:
                                return 1 / reduce(lambda r, i:
                                                r * (x.shift(-i).expand()),
                                                range(1, abs(int(k)) + 1), 1)
                        else:
                            return 1 / reduce(lambda r, i:
                                            r * (x - i),
                                            range(1, abs(int(k)) + 1), 1)

    def _eval_rewrite_as_gamma(self, x, k, **kwargs):
        from sympy import Gamma
        return Gamma(x + k) / Gamma(x)

    def _eval_rewrite_as_FallingFactorial(self, x, k, **kwargs):
        return FallingFactorial(x + k - 1, k)

    def _eval_rewrite_as_factorial(self, x, k, **kwargs):
        if x.is_integer and k.is_integer:
            return factorial(k + x - 1) / factorial(x - 1)

    def _eval_rewrite_as_binomial(self, x, k, **kwargs):
        if k.is_integer:
            return factorial(k) * binomial(x + k - 1, k)

    def _eval_is_extended_integer(self):
        x, k = self.args
        return fuzzy_and((x.is_extended_integer, k.is_extended_integer, k.is_nonnegative))

    def _sage_(self):
        import sage.all as sage
        return sage.rising_factorial(self.args[0]._sage_(),
                                     self.args[1]._sage_())

    def _latex(self, p, exp=None):
        n, k = self.args
        if n.is_Add or n.is_Mul:
            base = r"\left(%s\right)" % p._print(n)
        else:
            base = p._print(n)

        tex = r"{%s}^\overline{%s}" % (base, p._print(k))

        return p._do_exponent(tex, exp)

    def _eval_is_zero(self):
        n, k = self.args
        if k >= 0 and n > 0:
            return False


class FallingFactorial(CombinatorialFunction):
    r"""
    Falling factorial (related to rising factorial) is a double valued
    function arising in concrete mathematics, hypergeometric functions
    and series expansions. It is defined by

    .. math:: \texttt{ff(x, k)} = (x)_k = x \cdot (x-1) \cdots (x-k+1)

    where `x` can be arbitrary expression and `k` is an integer. For
    more information check "Concrete mathematics" by Graham, pp. 66
    or [1]_.

    When `x` is a `~.Poly` instance of degree $\ge 1$ with single variable,
    `(x)_k = x(y) \cdot x(y-1) \cdots x(y-k+1)`, where `y` is the
    variable of `x`. This is as described in

    >>> from sympy import ff, Poly, Symbol
    >>> from sympy.abc import x
    >>> n = Symbol('n', integer=True)

    >>> ff(x, 0)
    1
    >>> ff(5, 5)
    120
    >>> ff(x, 5) == x*(x - 1)*(x - 2)*(x - 3)*(x - 4)
    True
    >>> ff(Poly(x**2, x), 2)
    Poly(x**4 - 2*x**3 + x**2, x, domain='ZZ')
    >>> ff(n, n)
    factorial(n)

    Rewriting is complicated unless the relationship between
    the arguments is known, but falling factorial can
    be rewritten in terms of Gamma, factorial and binomial
    and rising factorial.

    >>> from sympy import factorial, rf, Gamma, binomial, Symbol
    >>> n = Symbol('n', integer=True, positive=True)
    >>> F = ff(n, n - 2)
    >>> for i in (rf, ff, factorial, binomial, Gamma):
    ...  F.rewrite(i)
    ...
    RisingFactorial(3, n - 2)
    FallingFactorial(n, n - 2)
    factorial(n)/2
    binomial(n, n - 2)*factorial(n - 2)
    Gamma(n + 1)/2

    See Also
    ========

    factorial, factorial2, RisingFactorial

    References
    ==========

    .. [1] https://mathworld.wolfram.com/FallingFactorial.html
    .. [2] Peter Paule, "Greatest Factorial Factorization and Symbolic
           Summation", Journal of Symbolic Computation, vol. 20, pp. 235-268,
           1995.

    """

    @classmethod
    def eval(cls, x, k):
        x = sympify(x)
        k = sympify(k)

        if x is S.NaN or k is S.NaN:
            return S.NaN
        elif k.is_integer and x == k:
            return factorial(x)
        elif k.is_Integer:
            if k is S.Zero:
                return S.One
            else:
                if k.is_positive:
                    if x is S.Infinity:
                        return S.Infinity
                    elif x is S.NegativeInfinity:
                        if k.is_odd:
                            return S.NegativeInfinity
                        else:
                            return S.Infinity
                    else:
                        if x.is_Poly:
                            gens = x.gens
                            if len(gens) != 1:
                                raise ValueError("ff only defined for "
                                            "polynomials on one generator")
                            else:
                                return reduce(lambda r, i:
                                              r * (x.shift(-i).expand()),
                                              range(0, int(k)), 1)
                        else:
                            return reduce(lambda r, i: r * (x - i),
                                          range(0, int(k)), 1)
                else:
                    if x is S.Infinity:
                        return S.Infinity
                    elif x is S.NegativeInfinity:
                        return S.Infinity
                    else:
                        if x.is_Poly:
                            gens = x.gens
                            if len(gens) != 1:
                                raise ValueError("rf only defined for "
                                            "polynomials on one generator")
                            else:
                                return 1 / reduce(lambda r, i:
                                                r * (x.shift(i).expand()),
                                                range(1, abs(int(k)) + 1), 1)
                        else:
                            return 1 / reduce(lambda r, i: r * (x + i),
                                            range(1, abs(int(k)) + 1), 1)

    def _eval_rewrite_as_gamma(self, x, k, **kwargs):
        from sympy import Gamma
        return (-1) ** k * Gamma(k - x) / Gamma(-x)

    def _eval_rewrite_as_RisingFactorial(self, x, k, **kwargs):
        return rf(x - k + 1, k)

    def _eval_rewrite_as_binomial(self, x, k, **kwargs):
        if k.is_integer:
            return factorial(k) * binomial(x, k)

    def _eval_rewrite_as_factorial(self, x, k, **kwargs):
        if x.is_integer and k.is_integer:
            return factorial(x) / factorial(x - k)

    def _eval_is_extended_integer(self):
        x, k = self.args
        return fuzzy_and((x.is_extended_integer, k.is_extended_integer, k.is_nonnegative))

    def _sage_(self):
        import sage.all as sage
        return sage.falling_factorial(self.args[0]._sage_(),
                                      self.args[1]._sage_())

    def _latex(self, p, exp=None):
        from sympy.printing.precedence import PRECEDENCE
        n, k = self.args
        if n.is_Add or n.is_Mul:
            base = r"{\left(%s\right)}" % p._print(n)
        else:
            base = p._print(n)
            
        sub = r"%s" % p._print(k)

        tex = r"%s^\underline{%s}" % (base, sub)

        return p._do_exponent(tex, exp)

    def _eval_is_zero(self):
        n, k = self.args
        if n.is_integer and k.is_integer:
            if k >= 0 and n >= k:
                return False
    
            if n >= 0 and k > n:
                return True 

    def _eval_is_finite(self):
        x, k = self.args
        k_is_finite = k.is_finite
        if not k_is_finite:
            return

        if k >= 0:
            return x.is_finite
        
        if k < 0:
            if x >= 0:
                return True
            
            if x < 0:
                if x.is_integer == False:
                    return x.is_real


rf = RisingFactorial
ff = FallingFactorial

###############################################################################
########################### BINOMIAL COEFFICIENTS #############################
###############################################################################


class Binomial(CombinatorialFunction):
    r"""Implementation of the binomial coefficient. It can be defined
    in two ways depending on its desired interpretation:

    .. math:: \binom{n}{k} = \frac{n!}{k!(n-k)!}\ \text{or}\
                \binom{n}{k} = \frac{(n)_k}{k!}

    First, in a strict combinatorial sense it defines the
    number of ways we can choose `k` elements from a set of
    `n` elements. In this case both arguments are nonnegative
    integers and binomial is computed using an efficient
    algorithm based on prime factorization.

    The other definition is generalization for arbitrary `n`,
    however `k` must also be nonnegative. This case is very
    useful when evaluating summations.

    For the sake of convenience, for negative integer `k` this function
    will return zero no matter the other argument.

    To expand the binomial when `n` is a symbol, use either
    ``expand_func()`` or ``expand(func=True)``. The former will keep
    the polynomial in factored form while the latter will expand the
    polynomial itself. See examples for details.

    Examples
    ========

    >>> from sympy import Symbol, Rational, binomial, expand_func
    >>> n = Symbol('n', integer=True, positive=True)

    >>> binomial(15, 8)
    6435

    >>> binomial(n, -1)
    0

    Rows of Pascal's triangle can be generated with the binomial function:

    >>> for N in range(8):
    ...     print([binomial(N, i) for i in range(N + 1)])
    ...
    [1]
    [1, 1]
    [1, 2, 1]
    [1, 3, 3, 1]
    [1, 4, 6, 4, 1]
    [1, 5, 10, 10, 5, 1]
    [1, 6, 15, 20, 15, 6, 1]
    [1, 7, 21, 35, 35, 21, 7, 1]

    As can a given diagonal, e.g. the 4th diagonal:

    >>> N = -4
    >>> [binomial(N, i) for i in range(1 - N)]
    [1, -4, 10, -20, 35]

    >>> binomial(Rational(5, 4), 3)
    -5/128
    >>> binomial(Rational(-5, 4), 3)
    -195/128

    >>> binomial(n, 3)
    binomial(n, 3)

    >>> binomial(n, 3).expand(func=True)
    n**3/6 - n**2/2 + n/3

    >>> expand_func(binomial(n, 3))
    n*(n - 2)*(n - 1)/6

    In many cases, we can also compute binomial coefficients modulo a
    prime p quickly using Lucas' Theorem [2]_, though we need to include
    `evaluate=False` to postpone evaluation:

    >>> from sympy import Mod
    >>> Mod(binomial(156675, 4433, evaluate=False), 10**5 + 3)
    28625

    Using a generalisation of Lucas's Theorem given by Granville [3]_,
    we can extend this to arbitrary n:
    n = Symbol(integer=True) #n = 10
    >>> Mod(binomial(n**18, n**12, evaluate=False), (n**5 + 3)**2)
    3744312326

    References
    ==========

    .. [1] https://www.johndcook.com/blog/binomial_coefficients/
    .. [2] https://en.wikipedia.org/wiki/Lucas%27s_theorem
    .. [3] Binomial coefficients modulo prime powers, Andrew Granville,
        Available: https://web.archive.org/web/20170202003812/http://www.dms.umontreal.ca/~andrew/PDF/BinCoeff.pdf
    """

    def fdiff(self, argindex=1):
        from sympy import polygamma
        if argindex == 1:
            # http://functions.wolfram.com/GammaBetaErf/Binomial/20/01/01/
            n, k = self.args
            return binomial(n, k) * (polygamma(0, n + 1) - \
                polygamma(0, n - k + 1))
        elif argindex == 2:
            # http://functions.wolfram.com/GammaBetaErf/Binomial/20/01/02/
            n, k = self.args
            return binomial(n, k) * (polygamma(0, n - k + 1) - \
                polygamma(0, k + 1))
        else:
            raise ArgumentIndexError(self, argindex)

    @classmethod
    def _eval(self, n, k):
        # n.is_Number and k.is_Integer and k != 1 and n != k

        if k.is_Integer:
            if n.is_Integer and n >= 0:
                n, k = int(n), int(k)

                if k > n:
                    return S.Zero
                elif k > n // 2:
                    k = n - k

                if HAS_GMPY:
                    from sympy.core.compatibility import gmpy
                    return Integer(gmpy.bincoef(n, k))

                d, result = n - k, 1
                for i in range(1, k + 1):
                    d += 1
                    result = result * d // i
                return Integer(result)
            else:
                d, result = n - k, 1
                for i in range(1, k + 1):
                    d += 1
                    result *= d
                    result /= i
                return result

    @classmethod
    def eval(cls, n, k):
        n, k = map(sympify, (n, k))
        d = n - k
        n_nonneg, n_isint = n.is_nonnegative, n.is_integer
        if k.is_zero or ((n_nonneg or n_isint is False)
                and d.is_zero):
            return S.One
        if (k - 1).is_zero or ((n_nonneg or n_isint is False)
                and (d - 1).is_zero):
            return n
        if k.is_integer:
            if k.is_negative or (n_nonneg and n_isint and d.is_negative):
                return S.Zero
            elif n.is_number:
                res = cls._eval(n, k)
                return res.expand(basic=True) if res else res
        elif n_nonneg is False and n_isint:
            # a special case when binomial evaluates to complex infinity
            return S.ComplexInfinity
        elif k.is_number:
            from sympy import Gamma
            return Gamma(n + 1) / (Gamma(k + 1) * Gamma(n - k + 1))

        if k > n or k > 0 and n < 0 or k < 0 and n > 0:
            return S.Zero
        if k == n:
            return S.One

    def _eval_Mod(self, q):
        n, k = self.args

        if any(x.is_integer == False for x in (n, k, q)):
            raise ValueError("Integers expected for binomial Mod")

        if all(x.is_Integer for x in (n, k, q)):
            n, k = map(int, (n, k))
            aq, res = abs(q), 1

            # handle negative integers k or n
            if k < 0:
                return S.Zero
            if n < 0:
                n = -n + k - 1
                res = -1 if k % 2 else 1

            # non negative integers k and n
            if k > n:
                return S.Zero

            isprime = aq.is_prime
            aq = int(aq)
            if isprime:
                if aq < n:
                    # use Lucas Theorem
                    N, K = n, k
                    while N or K:
                        res = res * binomial(N % aq, K % aq) % aq
                        N, K = N // aq, K // aq

                else:
                    # use Factorial Modulo
                    d = n - k
                    if k > d:
                        k, d = d, k
                    kf = 1
                    for i in range(2, k + 1):
                        kf = kf * i % aq
                    df = kf
                    for i in range(k + 1, d + 1):
                        df = df * i % aq
                    res *= df
                    for i in range(d + 1, n + 1):
                        res = res * i % aq

                    res *= pow(kf * df % aq, aq - 2, aq)
                    res %= aq

            else:
                # Binomial Factorization is performed by calculating the
                # exponents of primes <= n in `n! /(k! (n - k)!)`,
                # for non-negative integers n and k. As the exponent of
                # prime in n! is e_p(n) = [n/p] + [n/p**2] + ...
                # the exponent of prime in binomial(n, k) would be
                # e_p(n) - e_p(k) - e_p(n - k)
                M = int(_sqrt(n))
                for prime in sieve.primerange(2, n + 1):
                    if prime > n - k:
                        res = res * prime % aq
                    elif prime > n // 2:
                        continue
                    elif prime > M:
                        if n % prime < k % prime:
                            res = res * prime % aq
                    else:
                        N, K = n, k
                        exp = a = 0

                        while N > 0:
                            a = int((N % prime) < (K % prime + a))
                            N, K = N // prime, K // prime
                            exp += a

                        if exp > 0:
                            res *= pow(prime, exp, aq)
                            res %= aq

            return Integer(res % q)

    def _eval_expand_func(self, **hints):
        """
        Function to expand binomial(n, k) when m is positive integer
        Also,
        n is self.args[0] and k is self.args[1] while using binomial(n, k)
        """
        n = self.args[0]
        if n.is_Number:
            return binomial(*self.args)

        k = self.args[1]
        if k.is_Add and n in k.args:
            k = n - k

        if k.is_Integer:
            if k == S.Zero:
                return S.One
            elif k < 0:
                return S.Zero
            else:
                n, result = self.args[0], 1
                for i in range(1, k + 1):
                    result *= n - k + i
                    result /= i
                return result
        else:
            return binomial(*self.args)

    def _eval_rewrite_as_factorial(self, n, k, **kwargs):
        return factorial(n) / (factorial(k) * factorial(n - k))

    def _eval_rewrite_as_gamma(self, n, k, **kwargs):
        from sympy import Gamma
        return Gamma(n + 1) / (Gamma(k + 1) * Gamma(n - k + 1))

    def _eval_rewrite_as_tractable(self, n, k, **kwargs):
        return self._eval_rewrite_as_gamma(n, k).rewrite('tractable')

    def _eval_rewrite_as_FallingFactorial(self, n, k, **kwargs):
        if k.is_integer:
            return ff(n, k) / factorial(k)

    def _eval_is_finite(self):
        n, k = self.args
        return n.is_finite
        
    def _eval_is_zero(self):
        n, k = self.args
        if k.is_integer:
            if n.is_integer:
                if n >= k:
                    return False
            if n.is_integer is None:
                return
            return False

    def _eval_is_extended_integer(self):
        n, k = self.args
        if n.is_extended_integer and k.is_extended_integer:
            return True
        elif k.is_extended_integer == False:
            return False

    def _eval_is_extended_rational(self):
        n, k = self.args
        if n.is_extended_rational and k.is_extended_integer:
            return True
        elif k.is_extended_integer == False:
            return False

    def _eval_is_extended_real(self):
        n, k = self.args
        if n.is_extended_real and k.is_extended_real:
            return True
    
    def _eval_is_extended_negative(self):
        n, k = self.args
        if n.is_integer and k.is_integer:
            if n.is_extended_nonnegative or k.is_extended_negative or k.is_even:
                return False
            elif k.is_even == False:
                return True

    def _eval_is_extended_positive(self):
        n, k = self.args
        if n.is_integer and k.is_integer:
            if n >= k and k >= 0:
                return True

    def _eval_is_extended_complex(self):
        n, k = self.args
        if n.is_extended_complex and k.is_extended_complex:
            return True

    def domain_nonzero(self, x):
        from sympy import Range, oo
        n, k = self.args

        p = k.as_poly(x)
        if p.degree() == 1:
            alpha = p.coeff_monomial(x)
            beta = p.coeff_monomial(S.One)
            if alpha.is_number:
                if alpha == S.One:
                    # consider binomial(2*n, n), x = n
                    if not n._has(x):
                        return Range(-beta, n - beta + 1)
                elif alpha == S.NegativeOne:
                    return Range(beta - n, beta + 1)
        return Range(-oo, oo)

    @property
    def dtype(self): 
        from sympy.core.symbol import dtype
        n, _ = self.args
        if n.is_integer:
            return dtype.integer
        return n.type
    
    def _eval_shape(self):
        return ()
    
    def _latex(self, p, exp=None):
        tex = r"{\binom{%s}{%s}}" % (p._print(self.args[0]), p._print(self.args[1]))

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex
        
    def simplify(self, deep=False, **kwargs):
        n, k = self.args
        if k.is_Add:
            if n in k.args:
                k = n - k
                return self.func(n, k)
        return CombinatorialFunction.simplify(self, deep=deep, **kwargs)
    
binomial = binom = Binomial


class Multinomial(CombinatorialFunction):
    r"""Implementation of the multibinomial coefficient.
    https://en.wikipedia.org/wiki/Multinomial_theorem
    """

    @classmethod
    def _eval(self, n, *args):
        ...

    @classmethod
    def eval(cls, n, *args):
        ...

    def _eval_is_finite(self):
        n, *k = self.args
        return n.is_finite

    def _eval_is_zero(self):
        n, *k = self.args

    def _eval_is_extended_integer(self):
        n, *k = self.args
        if n.is_extended_integer:
            return True

    def _eval_is_extended_rational(self):
        n, *k = self.args
        if n.is_extended_rational:
            return True

    def _eval_is_extended_real(self):
        n, *k = self.args
        if n.is_extended_real:
            return True
    
    def _eval_is_extended_negative(self):
        n, *k = self.args

    def _eval_is_extended_complex(self):
        n, *k = self.args
        if n.is_extended_complex:
            return True

    def domain_nonzero(self, x):
        from sympy import Range, oo
        n, *k = self.args
        return Range(-oo, oo)

    @property
    def dtype(self): 
        from sympy.core.symbol import dtype
        n, *_ = self.args
        if n.is_integer:
            return dtype.integer
        return n.type
    
    def _eval_shape(self):
        return ()
    
    def _latex(self, p, exp=None):
        n, *args = self.args
        tex = r"{{%s} \choose {%s}}" % (p._print(n), ','.join(p._print(arg) for arg in args))

        if exp is not None:
            return r"%s^{%s}" % (tex, exp)
        else:
            return tex
        
    def simplify(self, deep=False, **kwargs):
        n, *args = self.args
        args_sorted = sorted(args, key=lambda arg: arg.sort_key())
        if args_sorted != args:
            return self.func(n, *args_sorted)
        
        if deep:
            return CombinatorialFunction.simplify(self, deep=deep, **kwargs)
        
        return self
