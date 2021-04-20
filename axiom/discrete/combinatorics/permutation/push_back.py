from sympy.core.relational import Equal
from axiom.utility import prove, apply

from sympy import Symbol, Slice
from sympy.core.numbers import oo
from sympy.sets.sets import Interval


@apply
def apply(*given):
    assert len(given) == 2    
    set_comprehension_equality, last_element_equality = given
    
    if last_element_equality.lhs.is_UNION:
        last_element_equality, set_comprehension_equality = set_comprehension_equality, last_element_equality
    p = last_element_equality.lhs.base
    n = last_element_equality.rhs
    
    assert set_comprehension_equality.is_Equal
    assert set_comprehension_equality.lhs._dummy_eq(p[:n].set_comprehension())
    assert set_comprehension_equality.rhs == Interval(0, n - 1, integer=True)
    
    return Equal(p[:n + 1].set_comprehension(), Interval(0, n, integer=True))




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True, given=True)
    
    Eq << apply(Equal(p[:n].set_comprehension(), Interval(0, n - 1, integer=True)),
                Equal(p[n], n))
    
    Eq << Eq[-1].this.lhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1].subs(Eq[0])
        
if __name__ == '__main__':
    prove()
