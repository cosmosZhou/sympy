from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    abs_x, a = axiom.is_LessEqual(given)
    x = axiom.is_Abs(abs_x)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    
    Eq << apply(abs(x) <= a)
    
    Eq << algebra.le.imply.le.split.abs.apply(Eq[0])
    
    Eq << -algebra.le.imply.le.split.abs.apply(Eq[0], negate=True)    
    

if __name__ == '__main__':
    prove()
