from util import *


def interval_is_real(interval):
    if interval.is_Interval:
        if interval.start.is_finite or interval.left_open:
            if interval.stop.is_finite or interval.right_open:
                return True
@apply
def apply(a_is_real, b_is_real):
    a, aR = a_is_real.of(Element)
    b, bR = b_is_real.of(Element)
    assert interval_is_real(aR)
    assert interval_is_real(bR)
    return Element(a * b, Reals)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Reals), Element(y, Reals))

    Eq << sets.el.imply.any_eq.apply(Eq[0], var='a')

    Eq << sets.el.imply.any_eq.apply(Eq[1], var='b')

    Eq << algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.mul)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], a * b, c)


if __name__ == '__main__':
    run()
# created on 2022-04-03
from . import add
from . import sub
