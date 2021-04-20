from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    is_imply_P, is_imply_Q = given
    p, x = axiom.is_Necessary(is_imply_P)    
    q, y = axiom.is_Necessary(is_imply_Q)
    
    return Necessary(p & q, x & y)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Necessary(x > 0, a > 0), Necessary(y > 0, b > 0))
    
    Eq << algebra.necessary.given.necessary.split.et.apply(Eq[-1])
    
    Eq << Eq[-2].this.rhs.apply(algebra.et.imply.cond, index=0)
    
    Eq << Eq[-1].this.rhs.apply(algebra.et.imply.cond, index=1)

    
if __name__ == '__main__':
    prove()
