from util import *


import axiom
from axiom.algebra.sum.to.add.doit.outer import doit


@apply
def apply(self):
    assert self.is_Cup
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(etype=dtype.real, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    n = 5
    Eq << apply(Cup[j:f(i), i:n](x[i, j]))

    s = Symbol.s(Lamda[i](Cup[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

from . import setlimit
