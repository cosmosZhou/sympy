from util import *


import axiom
from axiom.algebra.sum.doit.inner import doit


@apply(given=None)
def apply(self):
    assert self.is_Exists
    return Equivalent(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)

    n = 5
    Eq << apply(Exists[j:n, i:m](x[i, j] > 0))

    Eq << Equivalent(Exists[i:m](Equal(Bool(Exists[j:n](x[i, j] > 0)), 1)), Exists[j:n, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Bool, Exists).apply(algebra.any.to.ou.doit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

from . import setlimit
