from util import *


@apply(given=None)
def apply(self):
    from axiom.algebra.sum.to.add.doit.outer import doit
    return Equivalent(self, doit(All, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    n = 5
    Eq << apply(All[j:f(i), i:n](x[i, j] > 0))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(algebra.all.to.et.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.lhs.args[-1].apply(algebra.all.to.et.split, cond={n})


if __name__ == '__main__':
    run()

from . import setlimit
