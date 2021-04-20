from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return LessEqual(Ceiling(x / d) * d, x + d - 1, evaluate=evaluate)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    d = Symbol.d(integer=True, positive=True)
     
    Eq << apply(x, d)
    
    Eq << algebra.imply.lt.ceiling.apply(x / d)
    
    Eq << Eq[-1] * d
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])
    
if __name__ == '__main__':
    prove()

