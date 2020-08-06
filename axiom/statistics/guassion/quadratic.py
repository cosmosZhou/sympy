from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy import sqrt, pi, exp, Symbol, log
from sympy.integrals.integrals import Integral

from axiom.statistics.guassion import std


def coefficient(y, x):
    quadratic = -log(y.powsimp()).simplify()
    quadratic = quadratic.as_poly(x)
    if quadratic.degree() != 2:
        return None
    b = quadratic.coeff_monomial(x)
    a = quadratic.coeff_monomial(x * x)
    c = quadratic.coeff_monomial(1)
    return a, b, c


def doit(a, b, c):
    delta = (b ** 2 - 4 * a * c) / (4 * a)
    delta = delta.ratsimp()

    return sqrt(pi) * exp(delta) / sqrt(a)


@plausible
def apply(y, x=None):
    if x is None:
        if not isinstance(y, Integral):
            print('not isinstance(y, Integral)')
            return None
        if len(y.limits) > 1:
            return None
        (x, a, b), *_ = y.limits

        if a != -oo or b != oo:
            return None

        a, b, c = coefficient(y.function, x)
        if a <= 0:
            return None

        return Equality(y, doit(a, b, c))

    a, b, c = coefficient(y, x)

    if a <= 0:
        return None
    return Equality(Integral(y, (x, -oo, oo)), doit(a, b, c))


from sympy.utility import check


@check
def prove(Eq):
    a = Symbol("a", positive=True)
    b = Symbol("b", real=True)
    c = Symbol("c", real=True)
    x = Symbol("x", real=True)
    y = a * x * x + b * x + c

    Eq << apply(exp(-y), x)

    Eq << Eq[0].this.lhs.subs(x, x - b / (2 * a))

    Eq << Eq[-1].this.lhs.powsimp()

    Eq << std.apply()

    Eq << Eq[-1] * sqrt(2 * pi)

    Eq << Eq[-1].this.lhs.limits_subs(x, sqrt(2 * a) * x)

    Eq << Eq[-1] / sqrt(a)


if __name__ == '__main__':
    prove(__file__)

