from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom

# given: x[i] & x[j] = {}
# |Union x[i]| = Sum |x[i]|


@apply
def apply(given, n):
    eq, *limits = axiom.is_ForAll(given)    
    j, j_cond = axiom.limit_is_condition(limits)
    
    i, _j = axiom.is_Unequal(j_cond)
    if j != _j:
        i, _j = _j, i
    assert j == _j
    
    intersection, emptyset = axiom.is_Equal(eq)
    assert emptyset.is_EmptySet
    
    xi, xj = axiom.is_Intersection(intersection)
    if not xi.has(i):
        xi = xj
        assert xj.has(i)
        
    assert xj._subs(j, i) == xi
    
    return Equal(abs(UNION[i:0:n](xi)), Sum[i:0:n](abs(xi)))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=False)    
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finiteset=True)

    Eq << apply(ForAll(Equal(x[i] & x[j], x[i].etype.emptySet), (j, Unequal(j, i))), n)
    
    Eq << algebra.forall.imply.sufficient.apply(Eq[0])
    
    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.lt)
    
    j_ = Symbol.j(integer=True, nonnegative=True)
    Eq << Eq[-1].subs(j, j_)
    
    Eq << algebra.sufficient.imply.forall.apply(Eq[-1])
    
    Eq << sets.forall_is_emptyset.imply.eq.nonoverlapping.util.intlimit.apply(Eq[-1], n)
    
    
    
if __name__ == '__main__':
    prove()

