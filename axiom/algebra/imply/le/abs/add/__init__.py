from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x, y):
    assert not x.shape and not y.shape
    return LessEqual(abs(x + y), abs(x) + abs(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
     
    Eq << apply(x, y)
    
    Eq << (Eq[0].lhs ** 2).this.expand()
    
    Eq << (Eq[0].rhs ** 2).this.expand()
    
    Eq << algebra.imply.le.abs.apply(x * y)
    
    Eq << Eq[-1].this.rhs.astype(Mul)
    
    Eq << Eq[-1] * 2
    
    Eq << Eq[1] - Eq[2] + Eq[-1]
    
    Eq << Eq[-1] - Eq[-1].lhs.args[1]
    
    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)
    
    Eq << -Eq[-1]
    
    Eq << algebra.ge.imply.ge.sqrt.apply(Eq[-1])
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove()

del mul
from . import mul
