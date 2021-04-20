from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y, a, b):
    assert not x.shape and not y.shape
    return LessEqual(abs(x * y - a * b), abs(a) * abs(y - b) + abs(x - a) * abs(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
     
    Eq << apply(x, y, a, b)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.abs)
    
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.abs)
    
    Eq << Eq[-1].this.rhs.args[0].arg.expand()
    
    Eq << Eq[-1].this.rhs.args[0].arg.expand()
    
    Eq << algebra.imply.le.abs.add.apply(Eq[-1].rhs.args[0].arg, Eq[-1].rhs.args[1].arg)
    
    
    
    
if __name__ == '__main__':
    prove()

