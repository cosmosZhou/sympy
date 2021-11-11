from util import *





@apply
def apply(self):
    from axiom.algebra.add.to.sum import piece_together
    assert self.is_Union

    return Equal(self, piece_together(Cup, self))


@prove
def prove(Eq):
    from axiom import sets

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(etype=dtype.integer)
    Eq << apply(Cup[j:n, k:n](f(k)) | Cup[i:j, j:k, k:n](g(k)))

    Eq << Eq[0].this.rhs.apply(sets.cup.to.union)


if __name__ == '__main__':
    run()

from . import limits
# created on 2021-07-13
# updated on 2021-07-13
