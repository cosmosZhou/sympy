from util import *


import axiom
from axiom.algebra.sum.to.add.doit import doit


@apply(given=None)
def apply(self):
    assert self.is_ForAll
    return Equivalent(self, doit(self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)

    n = 5
    Eq << apply(ForAll[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.find(ForAll).apply(algebra.all.to.et.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(ForAll).apply(algebra.all.to.et.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(ForAll).apply(algebra.all.to.et.dissect, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(ForAll).apply(algebra.all.to.et.dissect, cond={n})


if __name__ == '__main__':
    run()
from . import outer
from . import setlimit
