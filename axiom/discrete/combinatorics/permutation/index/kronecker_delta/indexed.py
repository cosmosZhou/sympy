from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given, i=None, j=None):
    assert given.is_Equal
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    if i is None:
        i = Symbol.i(domain=Interval(0, n - 1, integer=True), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n
        
    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equal(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)
    
    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(i, j))
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq <<= Eq[-2].apply(algebra.cond.exists.imply.exists_et, simplify=None), \
    Eq[-1].apply(algebra.cond.exists.imply.exists_et, simplify=None)
    
    Eq << Eq[-2].this.function.apply(algebra.eq.ne.imply.ne.subs)    
    
    Eq << Eq[-1].this.function.apply(algebra.ne.cond.imply.et)    
    
    Eq << Eq[0].apply(algebra.eq.imply.eq.abs)
    
    Eq << sets.eq.imply.forall_is_emptyset.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].rhs.indices[0], j)
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, i)
    
    Eq << Eq[-1].this.find(NotContains).simplify()
    
    Eq << ~Eq[-1]

    
if __name__ == '__main__':
    prove()
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
