from util import *



@apply
def apply(given):
    contains, *limits = given.of(Any)
    x, A = contains.of(Contains)
    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.real, given=True)
    e = Symbol.e(real=True)

    Eq << apply(Any[e](Contains(e, A)))

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[1])


if __name__ == '__main__':
    run()

