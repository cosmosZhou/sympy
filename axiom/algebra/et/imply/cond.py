from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, index=None):
    eqs = axiom.is_And(given, copy=False)
    
    if index is None:        
        return eqs
    else:
        return eqs[index]

@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)))
    
    Eq << Sufficient(Eq[0], Eq[1], plausible=True)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Sufficient(Eq[0], Eq[2], plausible=True)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

    Eq << Sufficient(Eq[0], Eq[3], plausible=True)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])
if __name__ == '__main__':
    prove()

