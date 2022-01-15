from util import *


@apply
def apply(given, old, new):
    expr, (n, a, b) = given.of(Any[Tuple])
    assert n.is_integer
    assert old == n
    m = new + n + 1
    return Any[n:m - b:m - a](expr._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, m = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Any[n:0:m + 1](f(n) > 0), n, m - n)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[0], simplify=None)

    Eq << algebra.any.imply.any.limits.negate.infinity.apply(Eq[-1])

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.neg)

    Eq << algebra.any.imply.any.limits.subs.offset.apply(Eq[-1], -m)


if __name__ == '__main__':
    run()

from . import real
# created on 2019-02-18
