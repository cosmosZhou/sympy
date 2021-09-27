from util import *


@apply
def apply(given, index=-1):
    args = given.of(Equal[Union, EmptySet])
    lhs = Union(*args[:index])
    rhs = Union(*args[index:])
    emptySet = lhs.etype.emptySet
    return Equal(lhs, emptySet), Equal(rhs, emptySet)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq << sets.is_empty.imply.is_empty.apply(Eq[0], index=0)

    Eq << sets.is_empty.imply.is_empty.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()

