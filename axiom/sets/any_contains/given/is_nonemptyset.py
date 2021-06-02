from util import *
import axiom



@apply
def apply(given):
    contains, *limits = given.of(Exists)
    x, A = contains.of(Contains)
    return Unequal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.real, given=True)
    e = Symbol.e(real=True)

    Eq << apply(Exists[e](Contains(e, A)))

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[1])


if __name__ == '__main__':
    run()

