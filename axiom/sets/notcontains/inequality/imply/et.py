
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.relational import Unequal
from sympy.logic.boolalg import BooleanTrue, And, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from axiom import sets


@plausible
def apply(*given, invert=None):
    eq, inequality = given
    if not eq.is_NotContains:
        inequality, eq = given
        
    assert eq.is_NotContains
    assert inequality.is_Unequality
    
    lhs, rhs = inequality.args
    if invert:
        eq_original = eq
        eq = eq.invert()
        return And(eq_original, Unequal(lhs._subs(eq, BooleanFalse()), rhs._subs(eq, BooleanFalse())))
    
    return And(eq, Unequal(lhs._subs(eq, BooleanTrue()), rhs._subs(eq, BooleanTrue())))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), Unequal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))
    
    Eq << sets.notcontains.inequality.imply.inequality.apply(Eq[0], Eq[1])
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove(__file__)

