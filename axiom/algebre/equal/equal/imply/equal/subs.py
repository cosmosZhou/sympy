from axiom.utility import prove, apply
from sympy import *
import axiom


@apply(imply=True)
def apply(*given):    
    eq, f_eq = given
    lhs, rhs = axiom.is_Equal(eq)
    _lhs, _rhs = axiom.is_Equal(f_eq)
    return Equality(_lhs._subs(lhs, rhs), _rhs._subs(lhs, rhs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=(m,))
    g = Function.g(nargs=(n,), real=True, shape=(m,))
    
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equality(a, b), Equality(f(a), g(a)))
    
    Eq << Eq[1].subs(Eq[0])
        
    
if __name__ == '__main__':
    prove(__file__)
