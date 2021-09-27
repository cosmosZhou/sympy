from util import *


@apply
def apply(self):
    assert self.is_Mul
    from axiom.algebra.add.to.sum import piece_together

    return Equal(self, piece_together(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Product[i:k, k:n](f(k, i)) * Product[j:k, k:n](g(k, j)))

    Eq << Eq[-1].this.rhs.apply(algebra.prod.to.mul)


if __name__ == '__main__':
    run()

from . import division
from . import limits
