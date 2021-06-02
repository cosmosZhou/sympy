from util import *


# given: A in B
# => A | B = B
@apply
def apply(given):
    assert given.is_Contains
    A, B = given.args

    return Equal(A.set & B, A.set)


@prove
def prove(Eq):
    from axiom import sets
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    contains = Contains(e, s)

    Eq << apply(contains)

    Eq << sets.contains.imply.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.imply.eq.intersection.apply(Eq[-1])


if __name__ == '__main__':
    run()

