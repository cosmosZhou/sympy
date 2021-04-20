from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(given=None)
def apply(self):
    p, q = axiom.is_Sufficient(self)
        
    return Equivalent(self, And(*(Sufficient(p, eq) for eq in axiom.is_And(q))), evaluate=False)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)
    
    Eq << apply(Sufficient(x > y, (f(x) > g(y)) & (h(x) > g(y))))
    
    Eq << algebra.equivalent.given.sufficient.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.sufficient.imply.sufficient.split.et)
    
    Eq << Eq[-1].this.rhs.apply(algebra.sufficient.given.sufficient.split.et)
        
if __name__ == '__main__':
    prove()
