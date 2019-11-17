from sympy.core.numbers import oo
from sympy.utility import Eq, plausible
from sympy.core.relational import Equality
from sympy import sqrt, pi, exp, Symbol
from sympy.integrals.integrals import Integral


def apply():
    x = Symbol("x", real=True)
    return Equality(1 / sqrt(2 * pi) * Integral(exp(-x * x / 2), (x, -oo, oo)), 1, evaluate=False,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    Eq << apply()
    Eq << Eq[0] * sqrt(2 * pi)

    x, *_ = Eq[-1].this.lhs.limits[0]
    y = Symbol("y", real=True)

    Eq << Eq[-1].this.lhs.limits_subs(x, y) * Eq[-1]

    Eq << Eq[-1].this.lhs.as_multiple_limits()

    Eq << Eq[-1].this.lhs.as_polar_coordinate()

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-3].this.lhs.args[1].limits_subs(y, x)

    Eq << Eq[-1].sqrt()


# https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/
if __name__ == '__main__':
    prove(__file__)
