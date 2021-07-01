from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    return Equivalent(self, doit(All, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)

    n = 5
    Eq << apply(All[i:n](x[i] > 0))

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(All).apply(algebra.all.to.et.split, cond={n})


if __name__ == '__main__':
    run()
from . import outer
from . import setlimit
