from util import *


@apply
def apply(self, *, cond=None, wrt=None, simplify=True):
    from axiom.algebra.sum.to.add.split import split
    return Equal(self, split(Product, self, cond, wrt=wrt, simplify=simplify), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True)
    f = Function(real=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Product[x:A](f(x)), cond=B)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.rhs.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.prod)

    Eq << Eq[-1].this.rhs.expr.powsimp()

    Eq << Eq[-1].this.find(Element).apply(sets.el.to.ou.split, B)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.add)


if __name__ == '__main__':
    run()

