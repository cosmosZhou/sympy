from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(given, wrt=None):
    assert given._has(wrt)
    return Exists[wrt](given)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(f(e) > 0, wrt=e)
    
    S = Symbol.S(definition=Integers)
    Eq << ForAll[e:S](f(e) > 0, plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].definition
    
    Eq << Unequal(S, S.etype.emptySet, plausible=True)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << sets.is_nonemptyset.forall.imply.exists.apply(Eq[-1], Eq[2])
    
    Eq << Eq[-1].this.limits[0][1].definition
    
if __name__ == '__main__':
    prove(__file__)

