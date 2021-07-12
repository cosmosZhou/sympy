from util import *


@apply
def apply(given, wrt=None):
    AB = given.of(Unequal[EmptySet])

    A, B = AB.of(Complement)
    if wrt is None:
        wrt = A.element_symbol(B.free_symbols)
    assert wrt.type == B.etype
    return Any[wrt:A](Contains(wrt, AB))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A - B, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[0])

    i = Eq[-1].variable
    Eq << Suffice(Contains(i, A - B), And(Contains(i, A - B), Contains(i, A)), plausible=True)

    Eq << algebra.suffice.given.suffice.st.et.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.st.complement)

    Eq << Eq[2].this.function.apply(algebra.cond.suffice.imply.cond.transit, Eq[-2], simplify=None)

    Eq << Eq[-1].apply(algebra.any_et.imply.any.limits_absorb, index=0, simplify=None)


if __name__ == '__main__':
    run()

