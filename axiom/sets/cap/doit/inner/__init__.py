from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.inner import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(etype=dtype.real, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)

    n = 5
    Eq << apply(Cap[j:n, i:m](x[i, j]))

    s = Symbol.s(Lamda[i](Cap[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cap.to.intersection.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

from . import setlimit
