
from axiom.utility import prove, apply
from sympy import *
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
import axiom
from axiom import algebre


@apply
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


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), Piecewise((f(x), Contains(x, S)), (g(x), True)), invert=True)
    
    y = Symbol.y(definition=Eq[-1].lhs)
    Eq << y.this.definition
    
    Eq << algebre.condition.condition.imply.condition.apply(Eq[0], Eq[-1], invert=True)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)

