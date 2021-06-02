from util import *


@apply
def apply(given):
    e, (_, s)= given.of(Contains[Complement])
    return Equal(Bool(NotContains(e, s)), 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(e, S // s))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)

    Eq << sets.contains.imply.notcontains.st.complement.apply(Eq[0])


if __name__ == '__main__':
    run()

