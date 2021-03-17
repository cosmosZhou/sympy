from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(*given):
    assert len(given) == 2    
    set_comprehension_equality, last_element_equality = given
    
    if last_element_equality.lhs.is_UNION:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality

    p, n = axiom.is_Indexed(last_element_equality.lhs)
    _n = last_element_equality.rhs
    assert _n == n
    
    set_comprehension, interval = axiom.is_Equal(set_comprehension_equality)
    _p = axiom.is_set_comprehension(set_comprehension)
    assert p[:n + 1] == _p 
    assert interval == Interval(0, n, integer=True)
    
    return Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True, given=True)
    
    Eq << apply(Equality(p[:n + 1].set_comprehension(), Interval(0, n, integer=True)),
                Equality(p[n], n))
    
    Eq << Eq[0].this.lhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], {n}) 
    
    Eq << Eq[2].subs(Eq[-1].reversed).reversed
    
    Eq.plausible = NotContains(n, Eq[-1].rhs, plausible=True)
    
    Eq << ~Eq.plausible
    
    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.having.union_comprehension)
    
    i = Eq[-1].variable
    _i = i.copy(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq[0].lhs.this.bisect({_i, n})
    
    Eq.paradox = Eq[-1].subs(Eq[-2].reversed).subs(Eq[1])
    
    Eq << sets.imply.le.union.apply(*Eq.paradox.function.rhs.args)
    
    Eq << sets.imply.le.union_comprehension.apply(*Eq.paradox.function.rhs.args[1].args)
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq.paradox.apply(algebre.eq.imply.eq.abs)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-3].subs(Eq[-1].reversed)
    
    Eq << sets.notcontains.imply.eq.complement.apply(Eq.plausible)

        
if __name__ == '__main__':
    prove(__file__)
