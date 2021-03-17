from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
def apply(given, wrt=None):
    assert given._has(wrt)
    x = given.generate_free_symbol(**wrt.type.dict)
    domain = wrt.domain
    
    return Exists[x:domain](given._subs(wrt, x) & Equal(x, wrt))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    e = Symbol.e(domain=Interval(0, n - 1, integer=True))
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)
    
    Eq << ~Eq[-1]
    
    i = Eq[-1].variable
    Eq << Eq[0].forall((e,))
    
    Eq << Eq[-1].limits_subs(Eq[-1].variable, i)
    
    Eq <<= Eq[-1] & Eq[2]
        
    Eq << algebre.forall_et.imply.forall.apply(Eq[-1])    
    
    Eq << sets.forall_ne.imply.notcontains.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

