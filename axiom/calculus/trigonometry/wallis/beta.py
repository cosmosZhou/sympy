
from sympy.core.relational import Equality
from sympy.core.singleton import S
from sympy.functions.elementary.trigonometric import cos, sin
from axiom.utility import prove, apply
from sympy.core.sympify import sympify
from sympy.functions.special.beta_functions import beta
from sympy.integrals.integrals import Integral
import axiom
from sympy import Symbol
from axiom import calculus


@apply
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol.x(real=True)
    return Equality(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    beta(m / 2, n / 2) / 2)




@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(m, n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << calculus.trigonometry.wallis.gamma.apply(m, n)

    
if __name__ == '__main__':
    prove(__file__)

