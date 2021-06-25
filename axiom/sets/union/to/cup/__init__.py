from util import *





@apply
def apply(self):
    from axiom.algebra.add.to.sum import piece_together
    assert self.is_Union

    return Equal(self, piece_together(Cup, self))


@prove
def prove(Eq):
    from axiom import sets

    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(etype=dtype.integer)
    g = Function.g(etype=dtype.integer)
    Eq << apply(Cup[j:n, k:n](f(k)) | Cup[i:j, j:k, k:n](g(k)))

    Eq << Eq[0].this.rhs.apply(sets.cup.to.union)


if __name__ == '__main__':
    run()

del limits
from . import limits
