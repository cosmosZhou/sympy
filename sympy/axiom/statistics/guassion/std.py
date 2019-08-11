from sympy.core.numbers import oo
from sympy.utility import cout, Eq, plausible
from sympy.core.relational import Equality
from sympy import sqrt, pi, exp, Symbol
from sympy.integrals.integrals import Integral


def apply():
    x = Symbol("x", real=True)
    return Equality(1 / sqrt(2 * pi) * Integral(exp(-x * x / 2), (x, -oo, oo)), 1, evaluate=False,
                    plausible=plausible())


from sympy.utility import check
@check
def prove():
    cout << apply()
    cout << Eq[0] * sqrt(2 * pi)

    x, *_ = Eq[-1].left.limits[0]
    y = Symbol("y", real=True)

    cout << Eq[-1].left.subs_limits(x, y)

    cout << Eq[-1] * Eq[-2]

    cout << Eq[-1].left.as_multiple_limits()

    cout << Eq[-1].left.as_polar_coordinate()

    cout << Eq[-1].left.doit()

    cout << Eq[3].left.args[1].subs_limits(y, x)

    cout << Eq[-1].sqrt()


# https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/
if __name__ == '__main__':
    prove()
