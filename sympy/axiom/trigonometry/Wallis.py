from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.core.numbers import pi
from sympy.functions.elementary.trigonometric import cos, sin
from sympy.utility import plausible, cout, Eq, Integral
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from sympy.axiom.trigonometry import sine


def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol("x")
    return Equality(Integral[x:0:pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    beta(m / 2, n / 2) / 2,
#                     gamma(m / 2) * gamma(n / 2) / (2 * gamma((m + n) / 2)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    m = Symbol("m", integer=True, positive=True)
    n = Symbol("n", integer=True, positive=True)

#     x = Symbol("x")

#     Integral[x](sin(x) ** 2 * cos(x), x)
    cout << apply(m, n)

    (x, *_), *_ = Eq[0].lhs.limits

    cout << Eq[-1].right.expand(func=True)

    cout << Eq[1].subs(m, 1)

    cout << sine.Wallis.apply(n)

    cout << Eq[1].subs(m, m + 2)

    cout << Eq[-1].left.by_parts(u=cos(x) ** m)

    cout << Eq[-1] / (m / n)

    cout << Eq[-1].right.expand(func=True)

    cout << Eq[1].subs(n, n + 2).expand(func=True)

    cout << Eq[1].subs(m, 2)

    cout << Eq[-1].left.doit(manul=True)

    cout << Eq[-1].right.expand(func=True)


if __name__ == '__main__':
    prove()

