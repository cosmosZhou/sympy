from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.core.relational import StrictGreaterThan, Equality
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
import axiom


@plausible
def apply(*given, invert=None):
    eq, inequality = given
    assert eq.is_Contains    
    
    lhs, rhs = axiom.is_StrictGreaterThan(inequality)
    
    if invert:
        eq = eq.invert()
        return StrictGreaterThan(lhs._subs(eq, BooleanFalse()), rhs._subs(eq, BooleanFalse()))
    return StrictGreaterThan(lhs._subs(eq, BooleanTrue()), rhs._subs(eq, BooleanTrue()))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(Contains(x, S), StrictGreaterThan(Piecewise((f(x), Contains(x, S)), (g(x), True)), h(x)))
    
    Eq << Equality(bool(Contains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << StrictGreaterThan(Piecewise((f(x), Equality(bool(Contains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.definition
    
    Eq << Eq[-1].subs(Eq[-2])

    
if __name__ == '__main__':
    prove(__file__)

