from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    function, *limits = axiom.is_Product(self)
    assert len(limits) == 2
    (i, *_ab), (j, *ab) = self.limits
    assert i.type == j.type
    z = Dummy('z', **i.type.dict)
    this = self.limits_subs(i, z)
    this = this.limits_subs(j, i)
    this = this.limits_subs(z, j)
    
    return Equal(self, this)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    A = Symbol.A(etype=dtype.integer)

    f = Function.f(integer=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    h = Symbol.h(shape=(oo,), real=True)
    
    Eq << apply(Product[i:f(j), j:A](h[i] * g[i, j]))
    
    k = Symbol.k(integer=True)
    
    Eq << Eq[-1].this.rhs.limits_subs(i, k)



if __name__ == '__main__':
    prove()

