from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy import Symbol, Or, log, Unequal
from sympy.core.function import Function
import axiom

@apply(imply=True)
def apply(*given):
    is_nonzero, equality = given
    lhs = axiom.is_nonzero(is_nonzero)
    _lhs, rhs = axiom.is_Equal(equality)
    assert lhs == _lhs
        
    return Equality(1 / lhs, 1 / rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(Unequal(f(x), 0), Equality(f(x), g(x)))
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1].subs(Eq[1].reversed)


if __name__ == '__main__':
    prove(__file__)

