
from sympy.core.relational import Equality
from sympy.core.singleton import S
from sympy.functions.elementary.trigonometric import cos, sin
from axiom.utility import plausible
from sympy.core.sympify import sympify
from sympy.functions.special.gamma_functions import gamma
from sympy.integrals.integrals import Integral
import axiom
from sympy import Symbol
from axiom import algebre


@plausible
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol.x(real=True)
    return Equality(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)), 
                    gamma(m / 2) * gamma(n / 2) / (2 * gamma((m + n) / 2)))


from axiom.utility import check

@check
def prove(Eq, wolfram=None):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(m, n)
    
    (x, *_), *_ = Eq[0].lhs.limits

    Eq.one = Eq[0].subs(m, 1)

    Eq << axiom.calculus.trigonometry.sine.wallis.apply(n)

    Eq.induction = Eq[0].subs(m, m + 2)
    
    Eq << Eq.induction.this.lhs.function.expand()

    Eq << Eq[-1].this.lhs.by_parts(u=cos(x) ** m, wolfram=wolfram)

    Eq << Eq[-1] / (m / n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[0].subs(n, n + 2)
    
    Eq << Eq[-1].expand(func=True)

    Eq.two = Eq[0].subs(m, 2)

    Eq << Eq.two.this.lhs.doit(manul=True, wolfram=wolfram)

    Eq << Eq[-1].this.rhs.expand(func=True)
    
    Eq << Eq.induction.induct(imply=True)
    
    Eq << algebre.equality.equality.sufficient.imply.equality.double.induction.apply(Eq.one, Eq.two, Eq[-1], n=n, m=m, start=1)
   

if __name__ == '__main__':
    prove(__file__)

