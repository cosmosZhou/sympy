from util import *


@apply
def apply(given):
    fn, fn1 = given.of(Equivalent)
    return Equal(Bool(fn), Bool(fn1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    f, g = Symbol(integer=True, shape=(oo,))

    Eq << apply(Equivalent(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << algebra.iff.imply.infer.apply(Eq[0])

    Eq << algebra.infer.imply.eq.bool.apply(Eq[-1])

    Eq << algebra.iff.imply.assuming.apply(Eq[0])

    Eq << algebra.assuming.imply.eq.bool.apply(Eq[-1])

    Eq << Eq[-1] - Eq[-3]

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

from . import subs
from . import sum
# created on 2018-01-29
