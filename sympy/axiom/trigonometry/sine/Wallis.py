from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.core.numbers import pi
from sympy.functions.elementary.trigonometric import cos, sin
from sympy.functions.special.gamma_functions import gamma
from sympy.utility import plausible, cout, Eq, Integral
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from sympy.functions.elementary.miscellaneous import sqrt

from sympy import S


def apply(n):
    n = sympify(n)
    x = Symbol("x")
    return Equality(Integral[x:0:pi / 2](sin(x) ** (n - 1)),
                    sqrt(pi) * gamma(n / 2) / (2 * gamma(n / 2 + S.One / 2)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    n = Symbol("n", integer=True, positive=True)
    cout << apply(n)
    (x, *_), *_ = Eq[0].lhs.limits

    cout << Eq[0].subs(n, 1).doit()
    cout << Eq[0].subs(n, 2).doit()
    cout << Eq[0].subs(n, n + 2)
#     Integration by parts
    cout << Eq[-1].left.by_parts(dv=sin(x))
    cout << Eq[-1].left.args[1].function.powsimp()

    cout << Eq[0] - Eq[-1] / n

    cout << Eq[-1].left.as_one_term()

    cout << Eq[-1].left.trigsimp()

    cout << Eq[-1].left.function.powsimp()

    cout << Eq[1].left.function.powsimp().subs(Eq[-1])

    cout << Eq[-1].expand(func=True)
    cout << Eq[-1] + Eq[-1].rhs / n

    cout << Eq[-1].right.ratsimp()


if __name__ == '__main__':
    prove()

