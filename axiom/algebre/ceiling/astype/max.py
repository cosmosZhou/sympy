from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre

@apply
def apply(ceil):
    m = axiom.is_Ceiling(ceil)
    args = axiom.is_Max(m)
    args = [ceiling(arg) for arg in args]

    return Equality(ceil, Max(*args))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(ceiling(Max(x, y)))
    
    Eq << Eq[0].apply(algebre.eq.given.et.having.ceiling)
        
    Eq <<= algebre.imply.gt.ceiling.apply(x), algebre.imply.gt.ceiling.apply(y)
    
    Eq << algebre.gt.gt.imply.gt.max.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebre.max.astype.plus)
    
    Eq << Eq[-1] + 1
    
    
if __name__ == '__main__':
    prove(__file__)