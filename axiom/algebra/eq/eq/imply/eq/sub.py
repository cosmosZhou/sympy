from axiom.utility import prove, apply
from sympy import *
import axiom


@apply
def apply(*given):    
    eq, f_eq = given
    lhs, rhs = axiom.is_Equal(eq)
    _lhs, _rhs = axiom.is_Equal(f_eq)
    return Equal(lhs - _lhs, rhs - _rhs)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Equal(a, b), Equal(x, y))
    
    Eq << Eq[0] - Eq[1]
        
    
if __name__ == '__main__':
    prove()
