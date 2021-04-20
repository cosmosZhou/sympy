from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    min_xy = axiom.is_Floor(self)
    
    if min_xy.is_Mul:
        for i, min_args in enumerate(min_xy.args):
            if min_args.is_Min:
                args = [*min_xy.args]
                del args[i]
                factor = Mul(*args)
                assert factor > 0
                return Equal(self, Min(*[Floor(arg * factor) for arg in min_args.args]))
            
    x = []
    for arg in axiom.is_Min(min_xy): 
        x.append(Floor(arg))
        
    return Equal(self, Min(*x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
#     z = Symbol.z(real=True)
#     Eq << apply(Min(floor(x), floor(y), floor(z)))
    Eq << apply(floor(Min(x, y)))
    
    Eq << Eq[0].apply(algebra.eq.given.et.split.floor)
    
    Eq <<= algebra.imply.lt.floor.apply(x), algebra.imply.lt.floor.apply(y)
    
    Eq << algebra.lt.lt.imply.lt.min.both.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.min.to.add)
    
    Eq << Eq[-1] - 1

    
if __name__ == '__main__':
    prove()
