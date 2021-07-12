from util import *


@apply(given=None)
def apply(given):
    x, complement = given.of(Contains)

    B, A = complement.of(Complement)
    return Equivalent(given, And(Contains(x, B), NotContains(x, A)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Contains(x, B - A))

    Eq.suffice, Eq.necessary = algebra.equivalent.given.et.suffice.apply(Eq[-1])

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.contains.st.complement)

    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.notcontains.st.complement)

    Eq << Eq.necessary.this.lhs.simplify()




if __name__ == '__main__':
    run()

