from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply(imply=True)
def apply(given):
    function, *limits = axiom.is_ForAll(given)
    for limit in limits:
        x, *ab = limit
        if len(ab) == 1:
            domain = ab[0]
            assert Equal(domain, domain.etype.emptySet) == False
        elif len(ab) == 2:
            a, b = ab
            assert not a.shape and not a.is_set and a.is_extended_real
            assert not b.shape and not b.is_set and b.is_extended_real
            assert a <= b
                         
    return Exists(function, *limits)


@prove
def prove(Eq):
    S = Interval(0, oo, integer=True)
    e = Symbol.e(integer=True)
    f = Function.f(integer=True, shape=())
    Eq << apply(ForAll[e:S](f(e) > 0))
    
    Eq << Unequal(S, S.etype.emptySet, plausible=True)
    
    Eq << sets.is_nonemptyset.forall.imply.exists.apply(Eq[-1], Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

