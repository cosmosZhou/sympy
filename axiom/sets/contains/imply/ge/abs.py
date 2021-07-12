from util import *


@apply
def apply(given):
    x, S = given.of(Contains)
    return GreaterEqual(abs(S), 1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    S = Symbol.S(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, S))

    Eq << sets.contains.imply.is_nonemptyset.apply(Eq[0])

    Eq << sets.is_nonemptyset.imply.is_positive.apply(Eq[-1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()