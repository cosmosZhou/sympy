from axiom.utility import plausible
from sympy.core.relational import Equality, Unequal
from sympy import Symbol
from sympy.core.function import Function
import axiom


@plausible
def apply(*given):    
    eq, f_eq = given
    if not eq.is_Equal:
        eq, f_eq = f_eq, eq    
    lhs, rhs = axiom.is_Equal(eq)
    _lhs, _rhs = axiom.is_Unequal(f_eq)
    return Unequal(_lhs._subs(lhs, rhs), _rhs._subs(lhs, rhs))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=(m,))
    g = Function.g(nargs=(n,), real=True, shape=(m,))
    
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Equality(a, b), Unequal(f(a), g(a)))
    
    Eq << Eq[1].subs(Eq[0])
        
    
if __name__ == '__main__':
    prove(__file__)
