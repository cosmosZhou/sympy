from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(given):
    delta, one = axiom.is_Equal(given)
    if not one.is_One:
        delta, one = one, delta
    assert one.is_One
    
    x, y = axiom.is_KroneckerDelta(delta)
         
    return Equivalent(given, Equal(x, y))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    
    Eq << apply(Equal(KroneckerDelta(x, y), 1))
    
    Eq << algebra.equivalent.given.cond.apply(Eq[-1])
    
    Eq << Eq[-2].this.lhs.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)
    
    
if __name__ == '__main__':
    prove()
