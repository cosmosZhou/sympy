from sympy import *
from axiom.utility import prove, apply

from axiom import algebre, sets


@apply
def apply(sgm):
    assert sgm.is_Sum
    
    return Equality(sgm, sgm.func(sgm.function * Boole(sgm.limits_condition), *((x,) for x, *_ in sgm.limits)))


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(real=True)
     
    Eq << apply(Sum[x:S](f(x)))
    
    Eq << Eq[0].this.rhs.function.args[1].astype(Piecewise)


if __name__ == '__main__':
    prove(__file__)

