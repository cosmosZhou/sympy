from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity, Union
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete import expr_with_limits
from sympy.sets.conditionset import conditionset


@plausible
def apply(given):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = expr_with_limits.Ref(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplifier()
    
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    return Equality(x[Ref[k:n](KroneckerDelta(x[k], j)) @ Ref[k:n](k)], j, given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    
    x = IndexedBase('x', (n,), integer=True)    
    
    k = Symbol('k', integer=True)    
    given = Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True))    

    Eq << apply(given)
    
    Eq << identity(Eq[-1].lhs.indices[0]).expand()
    
    Eq << identity(Eq[-1].rhs.function.args[1]).definition
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << identity(Eq[-1].rhs.subs(1, 0)).bisect(domain={0})
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    j = Eq[1].rhs
    Eq << Eq[0].intersect({j})
    
    Eq << Eq[-1].this.lhs.distribute()
    
    Eq << Eq[-1].this.lhs.function.subs(Eq[-1].lhs.limits[0][1].args[1][1])
    return

    Eq << Equality(Union[k:conditionset(k, Equality(x[k], j), Interval(0, n - 1, integer=True))]({x[k]}), {j}, plausible=True)
    
    Eq << Eq[-1].this.lhs.function.subs(Eq[-1].lhs.limits[0][1].args[1][1])
    
    Eq << Eq[-1].abs()
    
    Eq << Eq[-2].lhs.assertion(given=Eq[-1])


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
