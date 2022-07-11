from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr > 0)
    fa, R = contains.of(Element)
    assert R.is_Interval
    return Element(fa / a, R.copy(start=R.start / a, stop=R.stop / a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t > 0, Element(x, Interval(a, b, left_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[1])



    Eq <<= algebra.gt_zero.gt.imply.gt.div.apply(Eq[0], Eq[-2]), algebra.gt_zero.le.imply.le.div.apply(Eq[0], Eq[-1])

    Eq << sets.gt.le.imply.el.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-19
