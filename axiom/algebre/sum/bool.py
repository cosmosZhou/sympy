from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets


@apply
def apply(sgm):
    assert sgm.is_Sum
    
    return Equality(sgm, sgm.func(sgm.function * Boole(sgm.limits_condition), *((x,) for x, *_ in sgm.limits)))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(real=True)    
     
    Eq << apply(Sum[x:A, y:B](f(x, y)))
    
    Eq << Eq[0].this.rhs.function.args[1].apply(algebre.bool.astype.times)
    
    Eq << Sum[x](Eq[-1].rhs.function).this.function.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Times)
    
    Eq << algebre.eq.imply.eq.sum.apply(Eq[-1], (y,))
    
    Eq << Eq[1].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.args[0].astype(Piecewise)


if __name__ == '__main__':
    prove(__file__)

