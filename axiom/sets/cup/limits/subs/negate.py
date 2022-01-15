from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.sum.limits.subs.negate import limits_subs
    return Equal(self, limits_subs(Cup, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets

    i, a, b, c = Symbol(integer=True)
    f = Function(etype=dtype.real)
    Eq << apply(Cup[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(sets.cup.piece)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.subs.offset, -c)


if __name__ == '__main__':
    run()
# created on 2018-10-07
