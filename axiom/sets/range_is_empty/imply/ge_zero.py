from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return GreaterEqual(a - b, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << sets.range_is_empty.imply.ge.apply(Eq[0])
    Eq << algebra.ge.imply.ge_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-18
