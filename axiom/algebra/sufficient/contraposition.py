from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(self):
    p, q = axiom.is_Sufficient(self)        
    return Equivalent(self, Sufficient(q.invert(), p.invert()))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Sufficient(x > y, f(x) > g(y)))
    
    Eq << Eq[0].this.lhs.apply(algebra.sufficient.to.ou)
    
    Eq << Eq[-1].this.rhs.apply(algebra.sufficient.to.ou)
        
if __name__ == '__main__':
    prove()
    
#     https://en.wikipedia.org/wiki/Contraposition
