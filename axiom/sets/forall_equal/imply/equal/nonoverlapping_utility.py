from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@apply(imply=True)
def apply(given):
    assert given.is_ForAll
    eq = given.function
    assert eq.is_Equality
    limits = given.limits
    * limits, (_, j_domain) = limits
    assert j_domain.is_Complement
    
    n_interval, i = j_domain.args
    n = n_interval.stop
    i, *_ = i.args
    
    intersection, emptyset = eq.args
    assert emptyset.is_EmptySet
    
    xi, xj = intersection.args
    if not xi.has(i):
        xi = xj
        assert xj.has(i)
        
    eq = Equality(abs(UNION[i:0:n](xi)), Sum[i:0:n](abs(xi)))
    if limits:
        return ForAll(eq, *limits)
    else:
        return eq


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    baseset = Interval(0, n, integer=True)
    
    assert Contains(0, baseset)

    domain = n.set
    assert n in baseset
    assert baseset & domain == domain

    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)

    i_domain = Interval(0, n - 1, integer=True)
    
    Eq << apply(ForAll(Equality(x[i] & x[j], x[i].etype.emptySet), (j, i_domain - {i})))
    
    Eq.initial = Eq[-1].subs(n, 2)
    
    Eq << Eq.initial.doit()
    
    Eq << Eq[0].subs(i, 1)
    
    Eq << Eq[-1].subs(j, 0)
    
    Eq << sets.imply.equal.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args).subs(Eq[-1])
    
    Eq.induction = Eq[1].subs(n, n + 1)
    
    Eq << Eq.induction.lhs.arg.this.bisect({n})
    
    Eq << sets.imply.equal.principle.inclusion_exclusion.basic.apply(*Eq[-1].rhs.args)
    
    Eq << Eq[0].subs(i, n).limits_subs(j, i)
    
    Eq << Eq[-1].apply(sets.equal.imply.equal.union_comprehension, *Eq[-1].limits)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq.induction.rhs.this.bisect({n})
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq.initial, Eq[-1], n=n, start=2)    

    
if __name__ == '__main__':
    prove(__file__)

