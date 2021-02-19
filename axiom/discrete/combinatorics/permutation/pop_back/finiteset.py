from sympy import Symbol, Slice, dtype
from sympy.core.relational import Equality
from axiom.utility import prove, apply

from sympy.core.numbers import oo
from sympy.sets.sets import Interval
from axiom import sets, algebre
from sympy.sets.contains import NotContains
import axiom


@apply
def apply(*given):
    assert len(given) == 2    
    set_comprehension_equality, last_element_equality = given
    
    if last_element_equality.lhs.is_UNION:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality
    p, n = axiom.is_Indexed(last_element_equality.lhs)
    a, _n = axiom.is_Indexed(last_element_equality.rhs)    
    
    assert n == _n
    
    set_comprehension_p, set_comprehension_a = axiom.is_Equal(set_comprehension_equality)
    _p = axiom.is_set_comprehension(set_comprehension_p)
    _a = axiom.is_set_comprehension(set_comprehension_a)
    assert a[:n + 1] == _a
    assert p[:n + 1] == _p
    
    return Equality(p[:n].set_comprehension(), a[:n].set_comprehension())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    p = Symbol.p(shape=(oo,), etype=dtype.integer, given=True)
    a = Symbol.a(shape=(oo,), etype=dtype.integer, given=True)
    
    Eq << apply(Equality(p[:n + 1].set_comprehension(), a[:n + 1].set_comprehension()),
                Equality(p[n], a[n]))
    
    Eq << Eq[0].this.lhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.rhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1] - a[n].set
    return
    Eq << Eq[2].subs(Eq[-1].reversed).reversed
    
    Eq.plausible = NotContains(n, Eq[-1].rhs, plausible=True)
    
    Eq << ~Eq.plausible
    
    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.where.union_comprehension)
    
    i = Eq[-1].variable
    _i = i.copy(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq[0].lhs.this.bisect({_i, n})
    
    Eq.paradox = Eq[-1].subs(Eq[-2].reversed).subs(Eq[1])
    
    Eq << sets.imply.less_than.union.apply(*Eq.paradox.function.rhs.args)
    
    Eq << sets.imply.less_than.union_comprehension.apply(*Eq.paradox.function.rhs.args[1].args)
    
    Eq << Eq[-2] + Eq[-1]
    
    Eq << Eq.paradox.apply(algebre.equal.imply.equal.abs)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-3].subs(Eq[-1].reversed)
    
    Eq << sets.notcontains.imply.equal.complement.apply(Eq.plausible)

        
if __name__ == '__main__':
    prove(__file__)
