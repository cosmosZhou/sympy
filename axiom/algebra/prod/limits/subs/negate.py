from util import *


@apply
def apply(self, old, new):
    from axiom.algebra.sum.limits.subs.negate import limits_subs
    return Equal(self, limits_subs(Product, self, old, new), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, a, b, c = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Product[i:a:b](f(i)), i, c - i)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.negate.infinity)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.subs.offset, -c)

    Eq << Eq[-1].this.rhs.find(Element).apply(sets.el.add, c)

    Eq << Eq[-1].this.lhs.apply(algebra.prod.bool)


if __name__ == '__main__':
    run()
# created on 2020-02-27
