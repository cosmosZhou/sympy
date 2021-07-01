from util import *

# given: A != {}
# Any[x] (x in A)


@apply
def apply(given):
    assert given.is_Unequal
    A, B = given.args
    if B:
        assert A.is_EmptySet
        A = B
    x = A.element_symbol()
    return Any[x](Contains(x, A))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1].simplify()

    Eq << sets.notcontains.imply.is_emptyset.emptyset_definition.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()

from . import st
