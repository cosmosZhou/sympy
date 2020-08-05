from sympy.core.relational import Equality
from sympy.utility import plausible, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.concrete.expr_with_limits import Forall
from sympy.tensor.indexed import IndexedBase

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from axiom.discrete.sets import union

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@plausible
def apply(given):
    assert given.is_Forall
    eq = given.function
    assert eq.is_Equality
    limits = given.limits
    assert len(limits) == 1
    (j, j_domain), *_ = limits
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
        
    return Equality(abs(Union[i:0:n - 1](xi)), Sum[i:0:n - 1](abs(xi)), given=given)


from sympy.utility import check


@check
def prove(Eq):
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    
    baseset = Interval(0, n, integer=True)
    domain = n.set
    assert n in baseset
    assert baseset & domain == domain

    x = IndexedBase('x', shape=(oo,), dtype=dtype.integer, finite=True)

    i_domain = Interval(0, n - 1, integer=True)
    
    given = Forall(Equality(x[i] & x[j], S.EmptySet), (j, i_domain - {i}))
    Eq << apply(given)
    
    Eq << Eq[-1].subs(n, 2).doit()
    
    Eq << Eq[0].subs(i, 1)
    
    Eq << Eq[-1].subs(j, 0)
    
    Eq << union.inclusion_exclusion_principle.apply(*Eq[-1].lhs.args).subs(Eq[-1])
    
    Eq.plausible = Eq[1].subs(n, n + 1)
    
    Eq << identity(Eq.plausible.lhs.arg).bisect(domain={n})
    
    Eq << union.inclusion_exclusion_principle.apply(*Eq[-1].rhs.args)
    
    Eq << Eq[0].subs(i, n).limits_subs(j, i)
    
    Eq << Eq[-1].union_comprehension((i, 0, n - 1))
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << identity(Eq.plausible.rhs).bisect(domain={n})
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    
if __name__ == '__main__':
    prove(__file__)

