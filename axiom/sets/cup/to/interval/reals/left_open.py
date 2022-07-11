from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, left_open=True)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    x = Eq[-1].lhs
    Eq <<= sets.el_cup.given.any_el.apply(Eq[-1])

    Eq << algebra.any.given.cond.subs.apply(Eq[-1], Eq[-1].variable, Ceiling(x) - 1)

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << algebra.imply.gt.ceiling.apply(x)

    Eq << algebra.imply.le.ceiling.apply(x)


if __name__ == '__main__':
    run()
# created on 2021-02-18
