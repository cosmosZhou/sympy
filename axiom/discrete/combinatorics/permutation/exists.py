from sympy.core.symbol import dtype
from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy.concrete.expr_with_limits import ForAll, Exists
from sympy import Symbol
from sympy.core.numbers import oo
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval
from sympy.sets.contains import Contains
from axiom import sets


@plausible
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p[:n]:P](Exists[i:n](Equality(p[i], n - 1)))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, domain=[1, oo])
    Eq << apply(n)
    
    Eq << Eq[1].subs(Eq[0])
    
    Eq << sets.imply.forall.apply(Eq[-1], simplify=False)
    
    Eq << Contains(n - 1, Eq[-1].rhs, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq[-1].this.definition.reversed
    

if __name__ == '__main__':
    prove(__file__)
