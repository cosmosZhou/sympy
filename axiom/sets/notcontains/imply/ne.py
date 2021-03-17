from axiom.utility import prove, apply
from sympy import *
from axiom import sets
import axiom


# given e not in S
@apply
def apply(given, index=0):
    assert given.is_NotContains
    e, s = given.args
    s = axiom.is_FiniteSet(s, size=None)
    return Unequal(e, s[index])


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    Eq << apply(NotContains(e, {a, b}))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

