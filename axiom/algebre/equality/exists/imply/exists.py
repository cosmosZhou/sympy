from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol
from sympy.core.function import Function
import axiom
from sympy import Exists
from sympy.sets.contains import Contains
from sympy.core.symbol import dtype
from sympy.functions.elementary.piecewise import Piecewise

@plausible
def apply(*given):
    eq, exists = given
    eq, _eq = axiom.is_Equivalent(eq)
    function, *limits = axiom.is_Exists(exists)
    function = function._subs(eq, _eq)
    return Exists(function, *limits)

from axiom.utility import check

@check
def prove(Eq):
    from axiom.sets.contains.imply.equality.piecewise.expr_swap import bool
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(nargs=(n,), real=True, shape=())
    g = Function.g(nargs=(n,), real=True, shape=())
    a = Function.a(nargs=(n,), shape=(n,))
    b = Function.b(nargs=(n,), shape=(n,))
    x = Symbol.x(real=True, shape=(n,))
    S = Symbol.S(etype=dtype.real * n)
    Eq << apply(Equality(bool(Contains(a(x), S)), bool(Contains(b(x), S))),
    Exists[x](Piecewise((f(x), Contains(a(x), S)), (g(x),True)) > 0))
    Eq << Exists[x](Piecewise((f(x), Equality(bool(Contains(a(x), S)), 1)), (g(x),True)) > 0, plausible=True)
    Eq << Eq[-1].this.function.lhs.args[0].cond.lhs.definition
    Eq << Eq[-1].subs(Eq[0])
    Eq << Eq[-1].this.function.lhs.args[0].cond.lhs.definition
    
if __name__ == '__main__':
    prove(__file__)
