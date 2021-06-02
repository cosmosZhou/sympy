from util import *
import axiom

from axiom.algebra.add.to.sum import piece_together


@apply
def apply(self):
    assert self.is_Mul

    return Equal(self, piece_together(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(Product[i:k, k:n](f(k, i)) * Product[j:k, k:n](g(k, j)))

    Eq << Eq[-1].this.rhs.apply(algebra.product.to.mul)


if __name__ == '__main__':
    run()

del limits
from . import limits
from . import division
