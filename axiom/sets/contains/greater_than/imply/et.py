
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains, Contains
from sympy import Symbol
from sympy.core.relational import GreaterThan, Equality
from sympy.logic.boolalg import BooleanTrue, And, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from axiom import sets
import axiom


@plausible
def apply(*given, invert=None):
    eq, inequality = given
    if not eq.is_Contains:
        inequality, eq = given
        
    assert eq.is_Contains
    
    lhs, rhs = axiom.is_GreaterThan(inequality)
    
    if invert:
        _eq = eq.invert()
        return And(eq, GreaterThan(lhs._subs(_eq, BooleanFalse()), rhs._subs(_eq, BooleanFalse())))
    
    return And(eq, GreaterThan(lhs._subs(eq, BooleanTrue()), rhs._subs(eq, BooleanTrue())))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(Contains(x, S), GreaterThan(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)), invert=True)
    
    Eq << sets.contains.greater_than.imply.greater_than.apply(Eq[0], Eq[1], invert=True)
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove(__file__)

