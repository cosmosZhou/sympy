from util import *


import axiom
from axiom.algebra.sum.to.add.doit import doit


@apply(given=None)
def apply(self):
    assert self.is_Exists
    return Equivalent(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)

    n = 5
    Eq << apply(Exists[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.any.to.ou.dissect, {n})

    n -= 1
    Eq << Eq[-1].this.find(Exists).apply(algebra.any.to.ou.dissect, {n})

    n -= 1
    Eq << Eq[-1].this.find(Exists).apply(algebra.any.to.ou.dissect, {n})

    n -= 1
    Eq << Eq[-1].this.find(Exists).apply(algebra.any.to.ou.dissect, {n})


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
