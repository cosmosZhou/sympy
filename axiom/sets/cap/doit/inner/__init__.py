from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.inner import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Cap[j:n, i:m](x[i, j]))

    s = Symbol(Lamda[i](Cap[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cap.to.intersect.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

from . import setlimit
# created on 2021-01-20
