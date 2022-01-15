from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.sum.limits.subs.negate import limits_subs
    return Equal(self, limits_subs(Cap, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cap[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(sets.cap.piece)

    Eq << Eq[-1].this.rhs.apply(sets.cap.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.rhs.apply(sets.cap.limits.subs.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.add, c)

    Eq << Eq[-1].this.lhs.apply(sets.cap.piece)


if __name__ == '__main__':
    run()
# created on 2021-01-28
