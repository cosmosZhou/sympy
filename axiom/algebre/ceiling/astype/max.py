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
    
    Eq << Eq[0].apply(algebre.equal.given.et.where.ceiling)
        
    Eq <<= algebre.imply.strict_greater_than.ceiling.apply(x), algebre.imply.strict_greater_than.ceiling.apply(y)
    
    Eq << algebre.strict_greater_than.strict_greater_than.imply.strict_greater_than.max.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebre.max.astype.plus)
    
    Eq << Eq[-1] + 1
    
    
if __name__ == '__main__':
    prove(__file__)