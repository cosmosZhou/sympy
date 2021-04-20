from sympy import *
from axiom.utility import prove, apply
from axiom import sets


# given e not in S
@apply
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equal(e.set & s, e.emptySet)


@prove
def prove(Eq):
    s = Symbol.s(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(NotContains(e, s))

    Eq << ~Eq[-1]
    
    Eq << sets.is_nonemptyset.imply.exists_contains.having.intersection.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove()

