from util import *


@apply
def apply(given):
    n = given.of(Equal[Basic % 2, 1])
    return Equal((-1) ** n, -1)


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)

    Eq << apply(Equal(n % 2, 1))

    Eq << ~Eq[0]

    Eq << algebra.ne.imply.is_even.apply(Eq[-1])

    Eq << algebra.is_even.imply.eq.pow.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
