from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra

@apply
def apply(ceil):
    m = axiom.is_Ceiling(ceil)
    args = axiom.is_Max(m)
    args = [ceiling(arg) for arg in args]

    return Equal(ceil, Max(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(ceiling(Max(x, y)))
    
    Eq << Eq[0].apply(algebra.eq.given.et.split.ceiling)
        
    Eq <<= algebra.imply.gt.ceiling.apply(x), algebra.imply.gt.ceiling.apply(y)
    
    Eq << algebra.gt.gt.imply.gt.max.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.add)
    
    Eq << Eq[-1] + 1
    
    
if __name__ == '__main__':
    prove()