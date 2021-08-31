from util import *


@apply
def apply(given):
    a, b = given.of(Greater)
    assert a.is_integer and b.is_integer
    return Equal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])
    Eq << sets.ge.imply.range_is_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()