from sympy.core.relational import Equality, StrictLessThan
from axiom.utility import plausible
from sympy import Symbol, Or
from sympy.core.function import Function
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains

from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets


@plausible
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    assert len(or_eqs) == 2
    return StrictLessThan(Piecewise(*expr_cond_pair(StrictLessThan, or_eqs, wrt, reverse=True)).simplify(), wrt)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(StrictLessThan(f(x), p) & Contains(x, A) | StrictLessThan(g(x), p) & NotContains(x, A), wrt=p)
    
    Eq << Eq[1].bisect(Contains(x, A)).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(sets.notcontains.greater_than.imply.et, invert=True), Eq[-1].apply(sets.contains.greater_than.imply.et)
    
    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-2].astype(Or)

if __name__ == '__main__':
    prove(__file__)

