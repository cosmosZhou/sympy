from util import *


@apply
def apply(given):
    e, (A, B) = given.of(Contains[Complement])

    return And(Contains(e, A), NotContains(e, B))


@prove
def prove(Eq):
    from axiom import sets, algebra
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A // B))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[0].apply(sets.contains.imply.contains.st.complement)

    Eq << Eq[0].apply(sets.contains.imply.notcontains.st.complement)


if __name__ == '__main__':
    run()

