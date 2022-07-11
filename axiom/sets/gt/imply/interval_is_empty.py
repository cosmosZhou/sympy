from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Greater)

    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq << sets.ne_empty.imply.any_el.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.et)

    Eq << Eq[-1].this.expr.apply(algebra.le.ge.imply.le.transit)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-09-10
