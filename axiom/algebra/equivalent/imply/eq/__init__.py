from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Equivalent)
    return Equal(Bool(fn), Bool(fn1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << algebra.equivalent.imply.suffice.apply(Eq[0])

    Eq << algebra.suffice.imply.eq.bool.apply(Eq[-1])

    Eq << algebra.equivalent.imply.necessary.apply(Eq[0])

    Eq << algebra.necessary.imply.eq.bool.apply(Eq[-1])

    Eq << Eq[-1] - Eq[-3]

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

from . import subs
from . import sum
