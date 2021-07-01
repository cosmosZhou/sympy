from util import *



@apply
def apply(given, S):
    lhs, rhs = given.of(Contains)
    return Contains(lhs, rhs | S)


@prove
def prove(Eq):
    from axiom import sets, algebra
    e = Symbol.e(integer=True)
    U = Symbol.U(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Contains(e, U), S)

    Eq << sets.contains.given.ou.split.union.apply(Eq[1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)

if __name__ == '__main__':
    run()

