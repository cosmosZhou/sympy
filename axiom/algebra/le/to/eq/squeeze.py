from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given):
    x, a = axiom.is_LessEqual(given)
    assert x >= a
    return Equivalent(given, Equal(x, a))


@prove
def prove(Eq):
    x = Symbol.x(domain=Interval(1, oo))
    
    Eq << apply(LessEqual(x, 1))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[-1])
    
    Eq << Eq[-2].this.apply(algebra.sufficient.to.ou)
    
    Eq << Eq[-1].apply(algebra.necessary.given.ou)
    

if __name__ == '__main__':
    prove()

