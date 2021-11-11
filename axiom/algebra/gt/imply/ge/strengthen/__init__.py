from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    
    assert lhs.is_extended_integer and rhs.is_extended_integer
    return GreaterEqual(lhs, rhs + 1)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
from . import minus
# created on 2018-05-12
# updated on 2018-05-12
