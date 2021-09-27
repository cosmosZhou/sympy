from util import *


@apply
def apply(notcontains):
    x, ab = notcontains.of(NotElement)

    a, b = ab.of(Interval)

    assert ab.right_open

    return Equal(x, b) | NotElement(x, ab.copy(right_open=False))


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Interval(a, b, right_open=True)))

    Eq << sets.ou.imply.notin.interval.st.notin.apply(Eq[1])


if __name__ == '__main__':
    run()

