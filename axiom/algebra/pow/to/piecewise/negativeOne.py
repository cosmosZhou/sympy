from util import *


@apply
def apply(self):
    n = self.of((-1) ** Expr)
    assert n.is_integer
    return Equal(self, Piecewise((1, Equal(n % 2, 0)), (-1, True)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True)

    Eq << apply((-1) ** n)

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[1].this.find(Equal & ~Equal).apply(algebra.is_even.to.eq)

    Eq << Eq[-1].this.find(Unequal).apply(algebra.mod_is_nonzero.to.is_odd)

    Eq << Eq[-1].this.find(Equal & ~Equal).apply(algebra.is_odd.to.eq)

    Eq << sets.imply.contains.pow.apply((-1) ** n)

    Eq << sets.contains.imply.ou.split.finiteset.apply(Eq[-1])


if __name__ == '__main__':
    run()

