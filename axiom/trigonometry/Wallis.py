from sympy.core.symbol import Symbol
from sympy.core.relational import Equality
from sympy.core.numbers import pi
from sympy.functions.elementary.trigonometric import cos, sin
from sympy.utility import plausible, Integral
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from axiom.trigonometry import sine


@plausible
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol("x")
    return Equality(Integral[x:0:pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    beta(m / 2, n / 2) / 2)


from sympy.utility import check


@check
def prove(Eq):
    m = Symbol("m", integer=True, positive=True)
    n = Symbol("n", integer=True, positive=True)

    Eq << apply(m, n)

    (x, *_), *_ = Eq[0].lhs.limits

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[1].subs(m, 1)

    Eq << sine.Wallis.apply(n)

    Eq << Eq[1].subs(m, m + 2)

    Eq << Eq[-1].this.lhs.by_parts(u=cos(x) ** m)

    Eq << Eq[-1] / (m / n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[1].subs(n, n + 2).expand(func=True)

    Eq << Eq[1].subs(m, 2)

    Eq << Eq[-1].this.lhs.doit(manul=True)

    Eq << Eq[-1].this.rhs.expand(func=True)


if __name__ == '__main__':
    prove(__file__)

