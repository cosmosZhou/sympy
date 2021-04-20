from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    b = axiom.is_Bool(self)    
    p, q = axiom.is_Or(b)
    
    return Equal(self, Bool(p) + Bool(q) - Bool(p & q))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
     
    Eq << apply(Bool(Or(Contains(x, A), Contains(x, B))))

    Eq << Eq[0].this.find(Bool).definition
    
    Eq << Add(*Eq[-1].rhs.args[:2]).this.find(Bool).definition
    
    Eq << Eq[-1].this.rhs.find(Bool).definition
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piecewise.st.two_pieces)
    
    Eq << Bool(Contains(x, A & B)).this.definition
               
    Eq << Eq[-2] - Eq[-1]
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piecewise.st.two_pieces)
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.find(Or).simplify()
    
if __name__ == '__main__':
    prove()

