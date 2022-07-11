from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    assert x.is_finite
    return Element(x, Interval(-oo, 0))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(x <= 0)

    Eq << sets.le.imply.is_real.apply(Eq[0], simplify=None)

    Eq << sets.el_interval.imply.ou.apply(Eq[-1], 0, left_open=True)

    Eq <<= Eq[0] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << algebra.et.imply.et.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-02-15
