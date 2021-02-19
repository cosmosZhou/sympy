from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from axiom import sets


# given e not in S
@apply
def apply(given):
    assert given.is_NotContains
    e, s = given.args
    return Equality(e.set & s, e.emptySet)


@prove
def prove(Eq):
    s = Symbol.s(etype=dtype.integer, given=True)
    e = Symbol.e(integer=True, given=True)

    Eq << apply(NotContains(e, s))

    Eq << ~Eq[-1]
    
    Eq << sets.is_nonemptyset.imply.exists_contains.overlapping.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

