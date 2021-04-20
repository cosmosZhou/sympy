from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    p, q = axiom.is_Add(self)
    p = axiom.is_Bool(p)    
    q = axiom.is_Bool(q)
    
    return Equal(self, Bool(p | q) + Bool(p & q))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
     
    Eq << apply(Bool(Contains(x, A)) + Bool(Contains(x, B)))
    
    Eq << Eq[-1].this.rhs.args[1].arg.apply(sets.contains.to.ou.split.union)
    
    Eq << Eq[-1].this.find(Bool[Or]).apply(algebra.bool.to.add)
    
    
if __name__ == '__main__':
    prove()

