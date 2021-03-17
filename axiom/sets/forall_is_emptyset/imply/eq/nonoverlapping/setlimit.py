from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@apply
def apply(given):
    assert given.is_ForAll
    eq = given.function
    assert eq.is_Equality
    limits = given.limits
    if len(limits) == 2: 
        (j, j_domain), i_limit = limits
        assert j_domain.is_Complement        
        _, i = j_domain.args
        assert i.is_FiniteSet and len(i) == 1
        i, *_ = i.args
    else:
        assert len(limits) == 1
        i, j_domain = limits[0]
        assert j_domain.is_Complement
        
        universe, j = j_domain.args
        assert j.is_FiniteSet and len(j) == 1
        j, *_ = j.args
        
        i_limit = (i, universe)

    intersection, emptyset = eq.args
    assert emptyset.is_EmptySet
    xi, xj = intersection.args
        
    if not xi._has(i):
        xi, xj = xj, xi
                        
    assert xi._subs(i, j) == xj
    return Equality(abs(UNION(xi, i_limit).simplify()), summation(abs(xi), i_limit))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
 
    j_domain = Interval(0, n - 1, integer=True) // {i}
    emptySet = x[i].etype.emptySet 
    Eq << apply(ForAll[j: j_domain, i: n](Equality(x[i] & x[j], emptySet)))

    y = Symbol.y(LAMBDA[i](Piecewise((x[i], i < n), (emptySet, True))))

    Eq.y_definition = y.equality_defined()
    
    Eq << Eq.y_definition.apply(algebre.cond.imply.forall.restrict, (i, 0, n))
    
    Eq.yi_definition = Eq[-1].this().function.rhs.simplify()
    
    Eq << Eq.yi_definition.reversed
    
    Eq.nonoverlapping = Eq[0].subs(Eq[-1]).subs(Eq[-1].limits_subs(i, j))
    
    Eq << Eq.y_definition.apply(algebre.cond.imply.forall.restrict, (i, n, oo))
    
    Eq << Eq[-1].this().function.rhs.simplify()
    
    Eq << Eq[-1].apply(sets.eq.imply.eq.intersect, y[j])
    
    Eq << Eq[-1].apply(algebre.cond.imply.forall.restrict, (j, j_domain))
    
    Eq <<= Eq[-1] & Eq.nonoverlapping

    Eq << sets.forall_is_emptyset.imply.eq.nonoverlapping.util.setlimit.apply(Eq[-1])    
    
    Eq << Eq[-1].subs(Eq.yi_definition)

    
if __name__ == '__main__':
    prove(__file__)

