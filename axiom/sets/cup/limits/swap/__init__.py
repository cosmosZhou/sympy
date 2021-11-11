from util import *


@apply
def apply(self):
    function, i_limit, j_limit = self.of(Cup)
    j, *_ = j_limit
    assert not i_limit._has(j)
    return Equal(self, Cup(function, j_limit, i_limit))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)
    Eq << apply(Cup[i:0:m, j:0:n](f[i] & g[i, j]))

    #Eq.initial = Eq[0].subs(n, 1)
    #Eq << Eq.initial.this.lhs.apply(sets.cup.doit.outer)
    #Eq << Eq[-1].this.rhs.apply(algebra.sum.doit.inner)
    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq.induct_dissected = Eq[-1].this.lhs.find(Cup).apply(sets.cup.to.union.doit.outer.setlimit)

    s = Symbol(Cup[j:0:n + 1](f[i] & g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(sets.eq.imply.eq.cup, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cup.to.union.split, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(sets.intersect.to.cup)

    Eq << Eq[-1].this.rhs.args[0].find(Cup).apply(sets.cup.to.union.doit.setlimit, simplify=None, evaluate=False)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.union)

    Eq << Eq.induct_dissected.subs(Eq[-1].reversed)

    Eq << sets.eq.imply.eq.union.apply(Eq[0], Eq[-1].lhs.args[0])

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
# created on 2021-02-11
# updated on 2021-02-11
