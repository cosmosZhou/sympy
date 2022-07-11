from util import *


@apply
def apply(given):
    x = given.of(Equal[Floor, 0])
    return Element(x, Interval(0, 1, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(Floor(x), 0))

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << algebra.imply.ge.floor.apply(x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << algebra.imply.lt.floor.apply(x)

    Eq << Eq[-1].subs(Eq[0])






if __name__ == '__main__':
    run()
# created on 2020-01-19
