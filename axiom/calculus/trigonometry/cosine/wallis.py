from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, geometry, calculus


@apply
def apply(n):
    n = sympify(n)
    x = Symbol.x(real=True)
    return Equality(Integral[x:0:pi / 2](cos(x) ** (n - 1)),
                    sqrt(pi) * gamma(n / 2) / (2 * gamma(n / 2 + S.One / 2)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=False)
    Eq << apply(n)
    (x, *_), *_ = Eq[0].lhs.limits

    Eq << Eq[0].subs(n, 1)
    
    Eq << Eq[-1].doit()
        
    Eq << Eq[0].subs(n, 2)
    
    Eq << Eq[-1].doit()

    Eq.induction = Eq[0].subs(n, n + 2)

    Eq << Eq.induction.lhs.this.expand()
#     Integration by parts
    Eq << Eq[-1].this.rhs.apply(calculus.integral.by_parts, dv=cos(x)) / n

    Eq << Eq[-1].this.lhs.args[1].function.powsimp()
    
    Eq << Eq[-1].this.rhs.function.powsimp()
    
    Eq << geometry.plane.trigonometry.sine.squared.apply(x)

    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.astype(Plus)

    Eq << Eq[-1].this.rhs.function.args[0].powsimp()
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].simplify()
    
    Eq << Eq[-1].solve(-Eq[-1].rhs.args[1])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq.induction.this.rhs.expand(func=True)

    Eq << Eq.induction.induct()
    
    Eq << algebre.equal.equal.sufficient.imply.equal.induction.apply(Eq[1], Eq[2], Eq[-1], n=n, start=1)


if __name__ == '__main__':
    prove(__file__)

