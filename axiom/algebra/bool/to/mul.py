from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_Bool
    et = axiom.is_Bool(self)
    eqs = axiom.is_And(et)
    
    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
     
    Eq << apply(Bool((x > y) & (a > b)))
    
    Eq << Eq[0].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[1].definition
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.lhs.definition
    


if __name__ == '__main__':
    prove()

