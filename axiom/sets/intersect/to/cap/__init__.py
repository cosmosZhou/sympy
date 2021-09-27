from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum import piece_together
    assert self.is_Intersection

    return Equal(self, piece_together(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    k, i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f, g = Function(etype=dtype.integer)
    Eq << apply(Cap[i:n, k:n, n:m](f(k)) & Cap[k:n, n:m](g(k)))

    Eq << Eq[0].this.rhs.apply(sets.cap.to.intersect)


if __name__ == '__main__':
    run()

from . import limits
