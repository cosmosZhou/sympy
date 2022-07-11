from util import *


@apply
def apply(given):
    x = given.of(Equal[Ceiling, 0])
    return Element(x, Interval(-1, 0, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(Ceiling(x), 0))

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << algebra.imply.le.ceiling.apply(x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << algebra.imply.gt.ceiling.apply(x)
    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-12
