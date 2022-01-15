from util import *


@apply
def apply(given, x=None, left_open=True, right_open=True):
    b, a = given.of(Greater)
    if x is None:
        x = given.generate_var(var='x', real=True)

    assert left_open or right_open
    return Unequal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(b > a)

    Eq << sets.lt.imply.any_el.interval.apply(Eq[0].reversed)

    Eq << sets.any_el.imply.ne_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-17
