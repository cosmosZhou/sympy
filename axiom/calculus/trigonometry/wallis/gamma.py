from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, calculus


@apply(imply=True)
def apply(m, n=1):
    m = sympify(m)
    n = sympify(n)

    x = Symbol.x(real=True)
    return Equality(Integral[x:0:S.Pi / 2](cos(x) ** (m - 1) * sin(x) ** (n - 1)),
                    gamma(m / 2) * gamma(n / 2) / (2 * gamma((m + n) / 2)))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(m, n)
    
    (x, *_), *_ = Eq[0].lhs.limits

    Eq.one = Eq[0].subs(m, 1)

    Eq << calculus.trigonometry.sine.wallis.apply(n)

    Eq.induction = Eq[0].subs(m, m + 2)
    
    Eq << Eq.induction.this.lhs.function.expand()

    Eq << Eq[-1].this.lhs.apply(calculus.integral.by_parts, u=cos(x) ** m)

    Eq << Eq[-1] / (m / n)

    Eq << Eq[-1].this.rhs.expand(func=True)

    Eq << Eq[0].subs(n, n + 2)
    
    Eq << Eq[-1].expand(func=True)

    Eq.two = Eq[0].subs(m, 2)

    t = Symbol.t(domain=Interval(0, 1)) 
    Eq << Eq.two.this.lhs.limits_subs(sin(x), t)
    
    Eq << calculus.integral.power.apply(n - 1, b=1, x=t)

    Eq << Eq[-2] - Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand(func=True)
    
    Eq << Eq.induction.induct(imply=True)
    
    Eq << algebre.equal.equal.sufficient.imply.equal.double.induction.apply(Eq.one, Eq.two, Eq[-1], n=n, m=m, start=1)
   

if __name__ == '__main__':
    prove(__file__)

