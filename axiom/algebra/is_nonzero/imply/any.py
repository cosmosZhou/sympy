from util import *


@apply
def apply(given, k=None):
    n = given.of(Unequal[Basic % 2, 0])
    if k is None:
        k = Symbol.k(integer=True)

    return Exists[k](Equal(n, k * 2 + 1))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)

    r = Symbol.r(integer=True)

    Eq << apply(Unequal(n % 2, 0))

    Eq << algebra.is_nonzero.imply.is_odd.apply(Eq[0])

    Eq << algebra.is_odd.imply.any.apply(Eq[-1], k=Eq[1].variable)


if __name__ == '__main__':
    run()
