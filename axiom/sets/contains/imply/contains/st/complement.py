from util import *


@apply
def apply(given):
    e, domain = given.of(Contains)
    S, s = domain.of(Complement)
    return Contains(e, S)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True)
    U = Symbol.U(etype=dtype.integer)
    s = Symbol.s(etype=dtype.integer)

    Eq << apply(Contains(x, U // s))

    Eq << Subset(Eq[0].rhs, Eq[1].rhs, plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

