from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equal
from sympy import Symbol
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.core.function import Function
from sympy.core.numbers import One


def process_given_conditions(*given, swap=False, delta=True):
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given
        
    lhs, rhs = axiom.is_Equal(eq)    
    assert f_eq.is_Boolean
    
    if delta:
        lhs, rhs = KroneckerDelta(lhs, rhs), One()
    return eq, f_eq._subs(lhs, rhs)


@apply(imply=True)
def apply(*given, **kwargs):    
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return f_eq


@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)
    Eq << apply(Equal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[2].reversed
    
    
if __name__ == '__main__':
    prove(__file__)

