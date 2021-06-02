from util import *


@apply
def apply(given, U):
    e, domain = given.of(Contains)
    S, s = domain.of(Complement)
    assert S in U
    return Contains(e, U // s)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True)
    U = Symbol.U(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    S = Symbol.S(A & U)
    s = Symbol.s(etype=dtype.integer)

    Eq << apply(Contains(x, S // s), U)

    Eq << Subset(Eq[1].rhs, Eq[2].rhs, plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

