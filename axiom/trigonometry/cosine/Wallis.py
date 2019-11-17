from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.core.numbers import pi
from sympy.functions.elementary.trigonometric import cos, sin
from sympy.functions.special.gamma_functions import gamma
from sympy.utility import plausible, Eq, Integral
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from sympy.functions.elementary.miscellaneous import sqrt

from sympy import S


def apply(n):
    n = sympify(n)
    x = Symbol("x")
    return Equality(Integral[x:0:pi / 2](cos(x) ** (n - 1)),
                    sqrt(pi) * gamma(n / 2) / (2 * gamma(n / 2 + S.One / 2)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol("n", integer=True, positive=True)
    Eq << apply(n)
    (x, *_), *_ = Eq[0].lhs.limits

    Eq << Eq[0].subs(n, 1).doit()
    Eq << Eq[0].subs(n, 2).doit()
    Eq << Eq[0].subs(n, n + 2)
#     Integration by parts
    Eq << Eq[-1].this.lhs.by_parts(dv=cos(x))
    Eq << Eq[-1].this.lhs.args[1].function.powsimp()

    Eq << Eq[0] - Eq[-1] / n

    Eq << Eq[-1].this.lhs.as_one_term()

    Eq << Eq[-1].this.lhs.trigsimp()

    Eq << Eq[-1].this.lhs.function.powsimp()

    Eq << Eq[1].this.lhs.function.powsimp().subs(Eq[-1])

    Eq << Eq[-1].expand(func=True)
    Eq << Eq[-1] + Eq[-1].rhs / n

    Eq << Eq[-1].this.rhs.ratsimp()


if __name__ == '__main__':
    prove(__file__)

