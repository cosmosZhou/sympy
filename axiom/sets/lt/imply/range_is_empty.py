from util import *


@apply
def apply(given):
    b, a = given.of(Less)
    assert a.is_integer and b.is_integer
    return Equal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << algebra.lt.imply.le.relax.apply(Eq[0])
    Eq << sets.le.imply.range_is_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-29
# updated on 2021-05-29
