
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains, Contains
from sympy import Symbol
from sympy.core.relational import Equal
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
import axiom
from axiom import sets


@plausible
def apply(given, piecewise, invert=None):
    assert given.is_NotContains    
    
    axiom.is_Piecewise(piecewise)
    
    eq = given
    if invert:
        eq = eq.invert()
        assert piecewise._has(eq)
        return Equal(piecewise, piecewise._subs(eq, BooleanFalse()))
    assert piecewise._has(eq)
    return Equal(piecewise, piecewise._subs(eq, BooleanTrue()))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), Piecewise((f(x), Contains(x, S)), (g(x), True)), invert=True)
    
    y = Symbol.y(definition=Eq[-1].lhs)
    Eq << y.this.definition
    
    Eq << sets.notcontains.equality.imply.equality.apply(Eq[0], Eq[-1], invert=True)
    
    Eq <<= Eq[-2] & Eq[-1]

    
if __name__ == '__main__':
    prove(__file__)

