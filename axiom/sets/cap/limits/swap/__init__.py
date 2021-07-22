from util import *


@apply
def apply(self):
    function, i_limit, j_limit = self.of(Cap)
    j, *_ = j_limit
    assert not i_limit._has(j)
    return Equal(self, Cap(function, j_limit, i_limit))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    f = Symbol.f(shape=(oo,), etype=dtype.real)
    g = Symbol.g(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cap[i:0:m, j:0:n](f[i] | g[i, j]))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cap.to.intersection.split, {n})

    Eq.induct_dissected = Eq[-1].this.lhs.find(Cap).apply(sets.cap.to.intersection.doit.outer.setlimit)

    s = Symbol.s(Cap[j:0:n + 1](f[i] | g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(sets.eq.imply.eq.cap, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cap.to.intersection.split, {n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.cap.to.intersection)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << sets.eq.imply.eq.intersection.apply(Eq[0], Eq[-1].lhs.args[0])

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
