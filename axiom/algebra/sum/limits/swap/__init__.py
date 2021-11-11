from util import *


@apply
def apply(self, i=0, j=1):
    assert i < j

    [function, *limits] = self.of(Sum)
    i_limit, j_limit = self.limits[i], self.limits[j]

    assert not i_limit._has(j_limit[0])
    limits[i], limits[j] = limits[j], limits[i]

    return Equal(self, Sum(function, *limits))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=False)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:0:m, j:0:n](f[i] * g[i, j]))

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(algebra.sum.to.add.doit.outer)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.doit.inner)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.sum.to.add.split, cond={n})

    s = Symbol(Sum[j:0:n + 1](f[i] * g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul.to.sum)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
# created on 2018-04-30
# updated on 2018-04-30
