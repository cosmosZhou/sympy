from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Greater)
    
    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.split.interval)

    Eq << Eq[-1].this.function.apply(algebra.le.ge.imply.le.transit)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()