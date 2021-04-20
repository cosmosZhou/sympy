from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
from axiom.algebra.sum.limits.domain_defined.insert import limits_insert
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_UNION
    return Equal(self, limits_insert(self))


@prove
def prove(Eq): 
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), integer=True)
    
    f = Function.f(etype=dtype.integer)
    h = Function.h(etype=dtype.real)
    
    Eq << apply(UNION[j:f(i), i](h(x[i], j)))
    
    Eq << Eq[-1].this.rhs.apply(sets.union_comprehension.limits.domain_defined.delete)

if __name__ == '__main__':
    prove()

