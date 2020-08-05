from sympy.core.relational import Equality
from sympy.utility import plausible, Ref
from sympy.core.symbol import Symbol, dtype
from sympy.concrete.expr_with_limits import Forall, UnionComprehension

from sympy.sets.sets import Interval, EmptySet
from sympy.core.numbers import oo
from axiom.discrete.sets.union_comprehension import nonoverlapping_converse_utility
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.summations import summation

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@plausible
def apply(given):
    assert given.is_Forall
    eq = given.function
    assert eq.is_Equality
    limits = given.limits
    assert len(limits) == 2
    (j, j_domain), i_limit = limits
    assert j_domain.is_Complement
    
    n_interval, i = j_domain.args
    n = n_interval.end
    i, *_ = i.args
    intersection, emptyset = eq.args
    assert emptyset.is_EmptySet
    xi, xj = intersection.args
    if not xi.has(i):
        xi = xj
        assert xj.has(i)
        
    return Equality(abs(UnionComprehension(xi, i_limit).simplify()), summation(abs(xi), i_limit), given=given)


from sympy.utility import check


@check
def prove(Eq):
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(oo,), dtype=dtype.integer, finite=True)
   
    j_domain = Interval(0, n - 1, integer=True) - {i}
    given = Forall(Equality(x[i] & x[j], EmptySet()), (j, j_domain), (i, 0, n - 1))
    Eq << apply(given)

    y = Symbol('y', shape=(oo,), dtype=dtype.integer, definition=Ref[i](Piecewise((x[i], i < n), (EmptySet(), True))))

    Eq << Equality.by_definition_of(y)
    
    Eq.y_definition = Eq[-1][i]
    
    Eq.yi_definition = Eq.y_definition.forall(i, 0, n - 1)
    
    Eq << Eq.yi_definition.reversed
    
    Eq << Eq[0].subs(Eq[-1]).subs(Eq[-1].limits_subs(i, j))
    
    Eq << Eq.y_definition.forall(i, n, oo)
    
    Eq << Eq[-1].intersect(y[j]).forall(j, j_domain)
    
    Eq << (Eq[-1] & Eq[-3])

    Eq << nonoverlapping_converse_utility.apply(Eq[-1])    
    
    Eq << Eq[-1].subs(Eq.yi_definition)

    
if __name__ == '__main__':
    prove(__file__)

