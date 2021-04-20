from sympy import *
from axiom.utility import prove, apply
from axiom import sets


# given e not in S
@apply
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equal(s, e.emptySet)


@prove
def prove(Eq):
    s = Symbol.s(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(NotContains(e, s))
    
    U = Symbol.U(e.universalSet)
    
    Eq << ForAll[e:U](NotContains(e, s), plausible=True)
    
    Eq << Eq[-1].this.limits[0][1].definition
    
    Eq << sets.forall_notcontains.imply.is_emptyset.apply(Eq[-1])
    
    Eq << Eq[-1].this.lhs.args[0].definition


if __name__ == '__main__':
    prove()

