from util import *


@apply
def apply(given):
    b, a = given.of(Greater)
    assert a.is_integer and b.is_integer
    return Unequal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(b > a)

    Eq << sets.lt.imply.any_el.range.apply(Eq[0].reversed)

    Eq << sets.any_el.imply.ne_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-04-18
