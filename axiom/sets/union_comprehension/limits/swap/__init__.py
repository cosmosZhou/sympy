from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    i_limit, j_limit = self.limits
    j, *_ = j_limit
    assert not i_limit._has(j)
    return Equal(self, self.func(self.function, j_limit, i_limit))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=False)

    f = Symbol.f(shape=(oo,), etype=dtype.real)
    g = Symbol.g(shape=(oo, oo), etype=dtype.real)    
    
    Eq << apply(UNION[i:0:m, j:0:n](f[i] & g[i, j]))
    
#     Eq.initial = Eq[0].subs(n, 1)
    
#     Eq << Eq.initial.this.lhs.apply(sets.union_comprehension.doit.outer)
    
#     Eq << Eq[-1].this.rhs.apply(algebra.sum.doit.inner)
    
    Eq.induct = Eq[0].subs(n, n + 1)
    
    Eq << Eq.induct.this.lhs.bisect({n})
    
    Eq.induct_dissected = Eq[-1].this.lhs.find(UNION).apply(sets.union_comprehension.to.union.doit.outer.setlimit)
    
    s = Symbol.s(UNION[j:0:n + 1](f[i] & g[i, j]))
    
    Eq << s.this.definition
    
    Eq << Eq[-1].apply(sets.eq.imply.eq.union_comprehension, (i, 0, m))
    
    Eq << Eq[-2].this.rhs.bisect({n})
    
    Eq << Eq[-1].this.rhs.args[1].apply(sets.intersection.to.union_comprehension)
    
    Eq << Eq[-1].this.rhs.args[0].find(UNION).apply(sets.union_comprehension.to.union.doit.setlimit, simplify=None, evaluate=False)
    
    Eq << Eq[-4].subs(Eq[-1])
    
    Eq << Eq[-1].this.lhs.apply(sets.union_comprehension.to.union)
    
    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)
    
    Eq << sets.eq.imply.eq.union.apply(Eq[0], Eq[-1].lhs.args[0])
    
    Eq << Eq.induct.induct()
    
    Eq << algebra.sufficient.imply.eq.induction.apply(Eq[-1], n=n, start=1)
    

if __name__ == '__main__':
    prove()

from . import intlimit
from . import subs
