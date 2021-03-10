from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self): 
    args = axiom.is_Max(self)
    
    x = []
    for arg in args:
        if arg.is_Ceiling:
            x.append(arg.arg)
        elif arg.is_integer:
            x.append(arg)
        else:            
            return
        
    return Equality(self, Ceiling(Max(*x)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Max(ceiling(x), ceiling(y)))
    
    Eq << Eq[0].apply(algebre.equal.given.et.where.ceiling)
    
    Eq <<= algebre.imply.strict_greater_than.ceiling.apply(x), algebre.imply.strict_greater_than.ceiling.apply(y)
    
    Eq << algebre.strict_greater_than.strict_greater_than.imply.strict_greater_than.max.both.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebre.max.astype.plus)
    
    Eq << Eq[-1] + 1
    
if __name__ == '__main__':
    prove(__file__)
