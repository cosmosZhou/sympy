
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.relational import Unequal, Equality, GreaterThan
from sympy.logic.boolalg import BooleanTrue, BooleanFalse
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.function import Function
from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
import axiom


@plausible
def apply(*given, invert=None):
    eq, inequality = given
    if not eq.is_NotContains:
        inequality, eq = given
        
    assert eq.is_NotContains
    lhs, rhs = axiom.is_GreaterThan(inequality)
    if invert:
        eq = eq.invert()
        return GreaterThan(lhs._subs(eq, BooleanFalse()), rhs._subs(eq, BooleanFalse()))
    
    return GreaterThan(lhs._subs(eq, BooleanTrue()), rhs._subs(eq, BooleanTrue()))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(nargs=(), shape=(), integer=True)    
    g = Function.g(nargs=(), shape=(), integer=True)
    h = Function.h(nargs=(), shape=(), integer=True)

    Eq << apply(NotContains(x, S), GreaterThan(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))
    
    Eq << Equality(bool(NotContains(x, S)), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << GreaterThan(Piecewise((f(x), Equality(bool(NotContains(x, S)), 1)), (g(x), True)), h(x), plausible=True)
    
    Eq << Eq[-1].this.lhs.args[0].cond.lhs.definition
    
    Eq << Eq[1].this.lhs.simplify()    
    
    Eq << Eq[-2].subs(Eq[-3])
    
if __name__ == '__main__':
    prove(__file__)

