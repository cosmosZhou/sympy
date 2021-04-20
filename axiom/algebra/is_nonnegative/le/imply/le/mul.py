from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    is_nonnegative, ge = given
    if 0 not in is_nonnegative.args:
        ge, is_nonnegative = given
    
    x = axiom.is_nonnegative(is_nonnegative)
    a, b = axiom.is_LessEqual(ge)
    
    return LessEqual(a * x, b * x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x >= 0, a <= b)
    
    Eq << Eq[1] - b
    
    Eq << algebra.is_nonnegative.is_nonpositive.imply.is_nonpositive.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << algebra.is_nonpositive.imply.le.apply(Eq[-1])
    
if __name__ == '__main__':
    prove()

