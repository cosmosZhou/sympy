"""

Contains
========
Geometric
Hermite
Logarithmic
NegativeBinomial
Poisson
Skellam
YuleSimon
Zeta
"""

from sympy import (Basic, factorial, exp, S, sympify, I, zeta, polylog, log, beta,
                   hyper, binomial, Piecewise, floor, besseli, sqrt, Sum, Dummy,
                   Lambda)
from sympy.stats.drv import SingleDiscreteDistribution, SingleDiscretePSpace
from sympy.stats.rv import _value_check, is_random
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.sets import PositiveIntegers, NonnegativeIntegers, Integers

__all__ = ['Geometric',
'Hermite',
'Logarithmic',
'NegativeBinomial',
'Poisson',
'Skellam',
'YuleSimon',
'Zeta'
]


def rv(symbol, cls, *args):
    args = list(map(sympify, args))
    dist = cls(*args)
    dist.check(*args)
    pspace = SingleDiscretePSpace(symbol, dist)
    if any(is_random(arg) for arg in args):
        from sympy.stats.compound_rv import CompoundPSpace, CompoundDistribution
        pspace = CompoundPSpace(symbol, CompoundDistribution(dist))
    return pspace.value


class DiscreteDistributionHandmade(SingleDiscreteDistribution):
    _argnames = ('pdf',)

    def __new__(cls, pdf, set=Integers):
        return Basic.__new__(cls, pdf, set)

    @property
    def set(self):
        return self.args[1]

    @staticmethod
    def check(pdf, set):
        x = Dummy('x')
        val = Sum(pdf(x), (x, set._inf, set._sup)).doit()
        _value_check(val == S.One, "The pdf is incorrect on the given set.")


def DiscreteRV(symbol, density, set=Integers):
    """
    Create a Discrete Random Variable given the following:

    Parameters
    ==========

    symbol : Symbol
        Represents name of the random variable.
    density : Expression containing symbol
        Represents probability density function.
    set : set
        Represents the region where the pdf is valid, by default is real line.

    Examples
    ========

    >>> from sympy.stats import DiscreteRV, P, E
    >>> from sympy import Rational, Symbol
    >>> x = Symbol('x')
    >>> n = 10
    >>> density = Rational(1, 10)
    >>> X = DiscreteRV(x, density, set=set(range(n)))
    >>> E(X)
    9/2
    >>> P(X>3)
    3/5

    Returns
    =======

    RandomSymbol

    """
    set = sympify(set)
    pdf = Piecewise((density, set.as_relational(symbol)), (0, True))
    pdf = Lambda(symbol, pdf)
    return rv(symbol.name, DiscreteDistributionHandmade, pdf, set)

#-------------------------------------------------------------------------------
# Geometric distribution ------------------------------------------------------------


class GeometricDistribution(SingleDiscreteDistribution):
    _argnames = ('p',)
    set = PositiveIntegers

    @staticmethod
    def check(p):
        _value_check((0 < p, p <= 1), "p must be between 0 and 1")

    def pdf(self, k):
        return (1 - self.p) ** (k - 1) * self.p

    def _characteristic_function(self, t):
        p = self.p
        return p * exp(I * t) / (1 - (1 - p) * exp(I * t))

    def _moment_generating_function(self, t):
        p = self.p
        return p * exp(t) / (1 - (1 - p) * exp(t))


def Geometric(name, p):
    r"""
    Create a discrete random variable with a Geometric distribution.

    The density of the Geometric distribution is given by

    .. math::
        f(k) := p (1 - p)^{k - 1}

    Parameters
    ==========

    p: A probability between 0 and 1

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Geometric, density, E, variance
    >>> from sympy import Symbol, S

    >>> p = S.One / 5
    >>> z = Symbol("z")

    >>> X = Geometric("x", p)

    >>> density(X)(z)
    (4/5)**(z - 1)/5

    >>> E(X)
    5

    >>> variance(X)
    20

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Geometric_distribution
    .. [2] http://mathworld.wolfram.com/GeometricDistribution.html

    """
    return rv(name, GeometricDistribution, p)

#-------------------------------------------------------------------------------
# Hermite distribution ---------------------------------------------------------


class HermiteDistribution(SingleDiscreteDistribution):
    _argnames = ('a1', 'a2')
    set = NonnegativeIntegers

    @staticmethod
    def check(a1, a2):
        _value_check(a1.is_nonnegative, 'Parameter a1 must be >= 0.')
        _value_check(a2.is_nonnegative, 'Parameter a2 must be >= 0.')

    def pdf(self, k):
        a1, a2 = self.a1, self.a2
        term1 = exp(-(a1 + a2))
        j = Dummy("j", integer=True)
        num = a1 ** (k - 2 * j) * a2 ** j
        den = factorial(k - 2 * j) * factorial(j)
        return term1 * Sum(num / den, (j, 0, k // 2)).doit()

    def _moment_generating_function(self, t):
        a1, a2 = self.a1, self.a2
        term1 = a1 * (exp(t) - 1)
        term2 = a2 * (exp(2 * t) - 1)
        return exp(term1 + term2)

    def _characteristic_function(self, t):
        a1, a2 = self.a1, self.a2
        term1 = a1 * (exp(I * t) - 1)
        term2 = a2 * (exp(2 * I * t) - 1)
        return exp(term1 + term2)


def Hermite(name, a1, a2):
    r"""
    Create a discrete random variable with a Hermite distribution.

    The density of the Hermite distribution is given by

    .. math::
        f(x):= e^{-a_1 -a_2}\sum_{j=0}^{\left \lfloor x/2 \right \rfloor}
                    \frac{a_{1}^{x-2j}a_{2}^{j}}{(x-2j)!j!}

    Parameters
    ==========

    a1: A Positive number greater than equal to 0.
    a2: A Positive number greater than equal to 0.

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Hermite, density, E, variance
    >>> from sympy import Symbol

    >>> a1 = Symbol("a1", positive=True)
    >>> a2 = Symbol("a2", positive=True)
    >>> x = Symbol("x")

    >>> H = Hermite("H", a1=5, a2=4)

    >>> density(H)(2)
    33*exp(-9)/2

    >>> E(H)
    13

    >>> variance(H)
    21

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Hermite_distribution

    """

    return rv(name, HermiteDistribution, a1, a2)

#-------------------------------------------------------------------------------
# Logarithmic distribution ------------------------------------------------------------


class LogarithmicDistribution(SingleDiscreteDistribution):
    _argnames = ('p',)

    set = PositiveIntegers

    @staticmethod
    def check(p):
        _value_check((p > 0, p < 1), "p should be between 0 and 1")

    def pdf(self, k):
        p = self.p
        return (-1) * p ** k / (k * log(1 - p))

    def _characteristic_function(self, t):
        p = self.p
        return log(1 - p * exp(I * t)) / log(1 - p)

    def _moment_generating_function(self, t):
        p = self.p
        return log(1 - p * exp(t)) / log(1 - p)


def Logarithmic(name, p):
    r"""
    Create a discrete random variable with a Logarithmic distribution.

    The density of the Logarithmic distribution is given by

    .. math::
        f(k) := \frac{-p^k}{k \ln{(1 - p)}}

    Parameters
    ==========

    p: A value between 0 and 1

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Logarithmic, density, E, variance
    >>> from sympy import Symbol, S

    >>> p = S.One / 5
    >>> z = Symbol("z")

    >>> X = Logarithmic("x", p)

    >>> density(X)(z)
    -5**(-z)/(z*log(4/5))

    >>> E(X)
    -1/(-4*log(5) + 8*log(2))

    >>> variance(X)
    -1/((-4*log(5) + 8*log(2))*(-2*log(5) + 4*log(2))) + 1/(-64*log(2)*log(5) + 64*log(2)**2 + 16*log(5)**2) - 10/(-32*log(5) + 64*log(2))

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Logarithmic_distribution
    .. [2] http://mathworld.wolfram.com/LogarithmicDistribution.html

    """
    return rv(name, LogarithmicDistribution, p)

#-------------------------------------------------------------------------------
# Negative binomial distribution ------------------------------------------------------------


class NegativeBinomialDistribution(SingleDiscreteDistribution):
    _argnames = ('r', 'p')
    set = NonnegativeIntegers

    @staticmethod
    def check(r, p):
        _value_check(r > 0, 'r should be positive')
        _value_check((p > 0, p < 1), 'p should be between 0 and 1')

    def pdf(self, k):
        r = self.r
        p = self.p

        return binomial(k + r - 1, k) * (1 - p) ** r * p ** k

    def _characteristic_function(self, t):
        r = self.r
        p = self.p

        return ((1 - p) / (1 - p * exp(I * t))) ** r

    def _moment_generating_function(self, t):
        r = self.r
        p = self.p

        return ((1 - p) / (1 - p * exp(t))) ** r


def NegativeBinomial(name, r, p):
    r"""
    Create a discrete random variable with a Negative Binomial distribution.

    The density of the Negative Binomial distribution is given by

    .. math::
        f(k) := \binom{k + r - 1}{k} (1 - p)^r p^k

    Parameters
    ==========

    r: A positive value
    p: A value between 0 and 1

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import NegativeBinomial, density, E, variance
    >>> from sympy import Symbol, S

    >>> r = 5
    >>> p = S.One / 5
    >>> z = Symbol("z")

    >>> X = NegativeBinomial("x", r, p)

    >>> density(X)(z)
    1024*5**(-z)*binomial(z + 4, z)/3125

    >>> E(X)
    5/4

    >>> variance(X)
    25/16

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Negative_binomial_distribution
    .. [2] http://mathworld.wolfram.com/NegativeBinomialDistribution.html

    """
    return rv(name, NegativeBinomialDistribution, r, p)

#-------------------------------------------------------------------------------
# Poisson distribution ------------------------------------------------------------


class PoissonDistribution(SingleDiscreteDistribution):
    _argnames = ('lamda',)

    domain = set = NonnegativeIntegers

    @staticmethod
    def check(lamda):
        _value_check(lamda > 0, "Lambda must be positive")

    def pdf(self, k):
        return self.lamda ** k / factorial(k) * exp(-self.lamda)

    def _characteristic_function(self, t):
        return exp(self.lamda * (exp(I * t) - 1))

    def _moment_generating_function(self, t):
        return exp(self.lamda * (exp(t) - 1))


def Poisson(name, lamda):
    r"""
    Create a discrete random variable with a Poisson distribution.

    The density of the Poisson distribution is given by

    .. math::
        f(k) := \frac{\lambda^{k} e^{- \lambda}}{k!}

    Parameters
    ==========

    lamda: Positive number, a rate

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Poisson, density, E, variance
    >>> from sympy import Symbol, simplify

    >>> rate = Symbol("lambda", positive=True)
    >>> z = Symbol("z")

    >>> X = Poisson("x", rate)

    >>> density(X)(z)
    lambda**z*exp(-lambda)/factorial(z)

    >>> E(X)
    lambda

    >>> simplify(variance(X))
    lambda

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Poisson_distribution
    .. [2] http://mathworld.wolfram.com/PoissonDistribution.html

    """
    return rv(name, PoissonDistribution, lamda)


class BinomialDistribution(SingleDiscreteDistribution):
    _argnames = ('n', 'p')    
    is_extended_negative = False
    
    @staticmethod
    def check(n, p):
        _value_check((n.is_integer, n.is_nonnegative),
                    "'n' must be nonnegative integer.")
        _value_check((p <= 1, p >= 0),
                    "p should be in range [0, 1].")

    @property
    def domain(self):
        from sympy import Range  
        return Range(self.n + 1) 

    set = domain
    
    def pdf(self, k):
        return binomial(self.n, k) * self.p ** k * (1 - self.p) ** (self.n - k)

    def sample(self):

        def search(x, y, u):
            while x < y:
                mid = (x + y) // 2
                if u <= self.cdf(mid):
                    y = mid
                else:
                    x = mid + 1
            return x

        u = random.uniform(0, 1)
        if u <= self.cdf(S.Zero):
            return S.Zero
        n = S.One
        while True:
            if u > self.cdf(2 * n):
                n *= 2
            else:
                return search(n, 2 * n, u)

    def _characteristic_function(self, t):
        return exp(self.lamda * (exp(I * t) - 1))

    def _moment_generating_function(self, t):
        return exp(self.lamda * (exp(t) - 1))


def Binomial(name, n, p):
    """
    Create a Finite Random Variable representing a binomial distribution.

    Returns a RandomSymbol.

    Examples
    ========

    >>> from sympy.stats import Binomial, density
    >>> from sympy import S

    >>> X = Binomial('X', 4, S.Half) # Four "coin flips"
    >>> density(X).dict
    {0: 1/16, 1: 1/4, 2: 3/8, 3: 1/4, 4: 1/16}

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Binomial_distribution
    .. [2] http://mathworld.wolfram.com/BinomialDistribution.html

    """

    return rv(name, BinomialDistribution, n, p)


class DieDistribution(SingleDiscreteDistribution):    
    _argnames = ('sides',)

    @staticmethod
    def check(sides):
        _value_check((sides.is_positive, sides.is_integer),
                    "number of sides must be a positive integer.")

    @property
    def is_symbolic(self):
        return not self.sides.is_number

    @property
    def high(self):
        return self.sides

    @property
    def low(self):
        return S.One

    @property
    def set(self):    
        from sympy import Range    
        return Range(1, self.sides + 1)

    domain = set
    
    def pdf(self, x):
        x = sympify(x)
        cond = (x >= 1) & (x <= self.sides)
        pdf = S.One / self.sides
        if cond:
            return pdf
        return Piecewise((pdf, cond), (S.Zero, True))

# -----------------------------------------------------------------------------
# Skellam distribution --------------------------------------------------------


class SkellamDistribution(SingleDiscreteDistribution):
    _argnames = ('mu1', 'mu2')
    set = Integers

    @staticmethod
    def check(mu1, mu2):
        _value_check(mu1 >= 0, 'Parameter mu1 must be >= 0')
        _value_check(mu2 >= 0, 'Parameter mu2 must be >= 0')

    def pdf(self, k):
        (mu1, mu2) = (self.mu1, self.mu2)
        term1 = exp(-(mu1 + mu2)) * (mu1 / mu2) ** (k / 2)
        term2 = besseli(k, 2 * sqrt(mu1 * mu2))
        return term1 * term2

    def _cdf(self, x):
        raise NotImplementedError(
            "Skellam doesn't have closed form for the CDF.")

    def _characteristic_function(self, t):
        (mu1, mu2) = (self.mu1, self.mu2)
        return exp(-(mu1 + mu2) + mu1 * exp(I * t) + mu2 * exp(-I * t))

    def _moment_generating_function(self, t):
        (mu1, mu2) = (self.mu1, self.mu2)
        return exp(-(mu1 + mu2) + mu1 * exp(t) + mu2 * exp(-t))


def Skellam(name, mu1, mu2):
    r"""
    Create a discrete random variable with a Skellam distribution.

    The Skellam is the distribution of the difference N1 - N2
    of two statistically independent random variables N1 and N2
    each Poisson-distributed with respective expected values mu1 and mu2.

    The density of the Skellam distribution is given by

    .. math::
        f(k) := e^{-(\mu_1+\mu_2)}(\frac{\mu_1}{\mu_2})^{k/2}I_k(2\sqrt{\mu_1\mu_2})

    Parameters
    ==========

    mu1: A non-negative value
    mu2: A non-negative value

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Skellam, density, E, variance
    >>> from sympy import Symbol, pprint

    >>> z = Symbol("z", integer=True)
    >>> mu1 = Symbol("mu1", positive=True)
    >>> mu2 = Symbol("mu2", positive=True)
    >>> X = Skellam("x", mu1, mu2)

    >>> pprint(density(X)(z), use_unicode=False)
         z
         -
         2
    /mu1\   -mu1 - mu2        /       _____   _____\
    |---| *e          *besseli\z, 2*\/ mu1 *\/ mu2 /
    \mu2/
    >>> E(X)
    mu1 - mu2
    >>> variance(X).expand()
    mu1 + mu2

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Skellam_distribution

    """
    return rv(name, SkellamDistribution, mu1, mu2)

#-------------------------------------------------------------------------------
# Yule-Simon distribution ------------------------------------------------------------


class YuleSimonDistribution(SingleDiscreteDistribution):
    _argnames = ('rho',)
    set = PositiveIntegers

    @staticmethod
    def check(rho):
        _value_check(rho > 0, 'rho should be positive')

    def pdf(self, k):
        rho = self.rho
        return rho * beta(k, rho + 1)

    def _cdf(self, x):
        return Piecewise((1 - floor(x) * beta(floor(x), self.rho + 1), x >= 1), (0, True))

    def _characteristic_function(self, t):
        rho = self.rho
        return rho * hyper((1, 1), (rho + 2,), exp(I * t)) * exp(I * t) / (rho + 1)

    def _moment_generating_function(self, t):
        rho = self.rho
        return rho * hyper((1, 1), (rho + 2,), exp(t)) * exp(t) / (rho + 1)


def YuleSimon(name, rho):
    r"""
    Create a discrete random variable with a Yule-Simon distribution.

    The density of the Yule-Simon distribution is given by

    .. math::
        f(k) := \rho B(k, \rho + 1)

    Parameters
    ==========

    rho: A positive value

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import YuleSimon, density, E, variance
    >>> from sympy import Symbol, simplify

    >>> p = 5
    >>> z = Symbol("z")

    >>> X = YuleSimon("x", p)

    >>> density(X)(z)
    5*beta(z, 6)

    >>> simplify(E(X))
    5/4

    >>> simplify(variance(X))
    25/48

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Yule%E2%80%93Simon_distribution

    """
    return rv(name, YuleSimonDistribution, rho)

#-------------------------------------------------------------------------------
# Zeta distribution ------------------------------------------------------------


class ZetaDistribution(SingleDiscreteDistribution):
    _argnames = ('s',)
    set = PositiveIntegers

    @staticmethod
    def check(s):
        _value_check(s > 1, 's should be greater than 1')

    def pdf(self, k):
        s = self.s
        return 1 / (k ** s * zeta(s))

    def _characteristic_function(self, t):
        return polylog(self.s, exp(I * t)) / zeta(self.s)

    def _moment_generating_function(self, t):
        return polylog(self.s, exp(t)) / zeta(self.s)


def Zeta(name, s):
    r"""
    Create a discrete random variable with a Zeta distribution.

    The density of the Zeta distribution is given by

    .. math::
        f(k) := \frac{1}{k^s \zeta{(s)}}

    Parameters
    ==========

    s: A value greater than 1

    Returns
    =======

    RandomSymbol

    Examples
    ========

    >>> from sympy.stats import Zeta, density, E, variance
    >>> from sympy import Symbol

    >>> s = 5
    >>> z = Symbol("z")

    >>> X = Zeta("x", s)

    >>> density(X)(z)
    1/(z**5*zeta(5))

    >>> E(X)
    pi**4/(90*zeta(5))

    >>> variance(X)
    -pi**8/(8100*zeta(5)**2) + zeta(3)/zeta(5)

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Zeta_distribution

    """
    return rv(name, ZetaDistribution, s)


# an AbstractDiscreteDistribution is a Discrete Distribution whose true probability density function is unevaluated!
# we only know its expression composed of other known random variables;
class AbstractDiscreteDistribution(SingleDiscreteDistribution):
#     _argnames = ['expression', 'set']

#     def __new__(cls, expr, domain=None):
#         if domain is None:
#             return SingleDiscreteDistribution.__new__(expr)
#         return SingleDiscreteDistribution.__new__(cls, expr, domain)

    @property
    def expression(self):
        return self.args[0]

    def pdf(self, x):
        from sympy.stats.rv import PDF
        if len(self.args) > 1:
            return self.expression(x)
        return PDF(self.expression)(x)

    @property
    def domain(self):
        if len(self.args) > 1: 
            return self.args[1]
               
        if self.expression >= 0:
            return Interval(0, oo)
        return Interval(-oo, oo)

    def __getattr__(self, attr):
        try:
            if attr == 'set':
                if self.expression >= 0:
                    return Interval(0, oo)
                return Interval(-oo, oo)

            if attr == 'expression':
                return self.args[0]
            return SingleDiscreteDistribution.__getattr__(self, attr)
        except Exception as e:
#             print(e)
            raise AttributeError("'%s' object has no attribute '%s'" % (type(self).__name__, attr))
