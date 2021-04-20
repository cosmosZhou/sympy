from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *, cond=None):
    p, q = axiom.is_Sufficient(given)
        
    return Sufficient(p & cond, q), Sufficient(p & cond.invert(), q)


@prove
def prove(Eq):
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    
    Eq << apply(Sufficient(Equal(f(x), f(y)), Equal(g(x), g(y))), cond=x > 0)
    
    Eq <<= Eq[-1] & Eq[-2]
    

        
if __name__ == '__main__':
    prove()

from . import ou
from . import et
