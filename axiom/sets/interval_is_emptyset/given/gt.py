from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return Greater(a, b)


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(Interval(a, b), a.emptySet))

    Eq << sets.gt.imply.is_emptyset.apply(Eq[1])












if __name__ == '__main__':
    run()