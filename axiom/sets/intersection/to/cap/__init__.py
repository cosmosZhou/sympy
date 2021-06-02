from util import *
import axiom

from axiom.algebra.add.to.sum import piece_together


@apply
def apply(self):
    assert self.is_Intersection

    return Equal(self, piece_together(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(etype=dtype.integer)
    g = Function.g(etype=dtype.integer)
    Eq << apply(Cap[i:n, k:n, n:m](f(k)) & Cap[k:n, n:m](g(k)))

    Eq << Eq[0].this.rhs.apply(sets.cap.to.intersection)


if __name__ == '__main__':
    run()

del limits
from . import limits
