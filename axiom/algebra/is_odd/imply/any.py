from util import *


@apply
def apply(given, k=None):
    n = given.of(Equal[Basic % 2, 1])
    if k is None:
        k = Symbol.k(integer=True)

    return Exists[k](Equal(n, k * 2 + 1))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)

    r = Symbol.r(integer=True)

    Eq << apply(Equal(n % 2, 1))

    k = Eq[1].variable

    Eq << algebra.eq.imply.any.definition.mod.apply(Eq[0], q=k)


if __name__ == '__main__':
    run()
