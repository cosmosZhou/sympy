from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, wrt=None):
    assert given._has(wrt)
    x = given.generate_free_symbol(**wrt.type.dict)
    domain = wrt.domain
    
    return Exists[x:domain](given._subs(wrt, x) & Equal(x, wrt))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    e = Symbol.e(domain=Interval(0, n - 1, integer=True), given=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].this.find(Unequal).apply(sets.ne.imply.notcontains)
    
    Eq << Eq[-1].apply(algebra.forall_ou.imply.forall.limits.absorb, index=1)
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()

