from util import *


@apply(given=None)
def apply(given):
    x, complement = given.of(Element)

    B, A = complement.of(Complement)
    return Equivalent(given, And(Element(x, B), NotElement(x, A)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Element(x, B - A))

    Eq.suffice, Eq.necessary = algebra.iff.given.et.infer.apply(Eq[-1])

    Eq << algebra.infer.given.et.infer.apply(Eq.suffice)

    Eq << Eq[-2].this.lhs.apply(sets.el.imply.el.st.complement)

    Eq << Eq[-1].this.lhs.apply(sets.el.imply.notin.st.complement)

    Eq << Eq.necessary.this.lhs.simplify()


if __name__ == '__main__':
    run()

# created on 2021-01-25
