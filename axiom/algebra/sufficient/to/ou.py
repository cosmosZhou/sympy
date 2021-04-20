from sympy import *
from axiom.utility import prove, apply
import axiom


@apply(given=None)
def apply(self):
    p, q = axiom.is_Sufficient(self)        
    return Equivalent(self, p.invert() | q, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Sufficient(x > y, f(x) > g(y)))
        
if __name__ == '__main__':
    prove()
