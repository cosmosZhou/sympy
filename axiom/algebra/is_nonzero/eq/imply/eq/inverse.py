from axiom.utility import prove, apply
from sympy import *
import axiom


@apply
def apply(*given):
    is_nonzero, equality = given
    if is_nonzero.is_Equal:
        equality, is_nonzero = given
        
    lhs = axiom.is_nonzero(is_nonzero)
    _lhs, rhs = axiom.is_Equal(equality)
    assert lhs == _lhs
        
    return Equal(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Unequal(f(x), 0), Equal(f(x), g(x)))
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    prove()

