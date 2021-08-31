from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.sum.doit.inner import doit
    return Equivalent(self, doit(All, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(All[j:n, i:m](x[i, j] > 0))

    Eq << Equivalent(All[i:m](Equal(Bool(All[j:n](x[i, j] > 0)), 1)), All[j:n, i:m](x[i, j] > 0), plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Bool, All).apply(algebra.all.to.et.doit)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

from . import setlimit
