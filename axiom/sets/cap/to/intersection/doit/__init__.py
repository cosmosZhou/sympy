from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    assert self.is_Cap
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import sets
    n = 5
    x = Symbol.x(etype=dtype.real, shape=(n,))
    i = Symbol.i(integer=True)

    Eq << apply(Cap[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(sets.cap.limits.domain_defined.insert)

    n -= 1
    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersection.dissect, {n})

    n -= 1
    Eq << Eq[-1].find(Cap).this.apply(sets.cap.to.intersection.dissect, {n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cap).this.apply(sets.cap.to.intersection.dissect, {n})

    n -= 1
    Eq << Eq[-1].rhs.find(Cap).this.apply(sets.cap.to.intersection.dissect, {n})

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
