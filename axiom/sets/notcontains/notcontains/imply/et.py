
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains, Contains
from sympy import Symbol
from sympy.logic.boolalg import BooleanTrue, And, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from axiom import sets
import axiom


@plausible
def apply(*given, invert=None, swap=None):
    eq, f_eq = given
    assert eq.is_NotContains and f_eq.is_NotContains
    if swap:
        f_eq, eq = given
    
    lhs, rhs = axiom.is_NotContains(f_eq)
    
    if invert:
        _eq = eq.invert()
        return And(eq, NotContains(lhs._subs(_eq, BooleanFalse()), rhs._subs(_eq, BooleanFalse())))
    
    return And(eq, NotContains(lhs._subs(eq, BooleanTrue()), rhs._subs(eq, BooleanTrue())))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), etype=dtype.integer)

    Eq << apply(NotContains(x, S), NotContains(Piecewise((f(x), Contains(x, S)), (g(x), True)), h(x)), invert=True)
    
    Eq << sets.notcontains.notcontains.imply.notcontains.substitute.apply(Eq[0], Eq[1], invert=True)
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove(__file__)

