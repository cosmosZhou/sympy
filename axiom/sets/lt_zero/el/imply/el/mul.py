from util import *


@apply
def apply(is_positive, contains):
    a = is_positive.of(Expr < 0)
    fa, R = contains.of(Element)
    assert R.is_Interval
    return Element(fa * a, Interval(R.stop * a, R.start * a, left_open=R.right_open, right_open=R.left_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    t, x, a, b = Symbol(real=True)
    Eq << apply(t < 0, Element(x, Interval(a, b, left_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[1])



    Eq <<= algebra.lt_zero.gt.imply.lt.mul.apply(Eq[0], Eq[-2]), algebra.lt_zero.le.imply.ge.mul.apply(Eq[0], Eq[-1])

    Eq << sets.lt.ge.imply.el.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-03
