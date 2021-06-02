from util import *


@apply
def apply(notcontains):
    x, ab = notcontains.of(NotContains)

    a, b = ab.of(Interval)

    assert ab.right_open

    return Equal(x, b) | NotContains(x, ab.copy(right_open=False))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(NotContains(x, Interval(a, b, right_open=True)))

    Eq << sets.ou.imply.notcontains.interval.apply(Eq[1])


if __name__ == '__main__':
    run()

