from util import *


@apply
def apply(self):
    i_limit, j_limit = self.limits
    j, *_ = j_limit
    assert not i_limit._has(j)
    return Equal(self, self.func(self.function, j_limit, i_limit))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:0:m, j:0:n](f[i] * g[i, j]))

    Eq.initial = Eq[0].subs(n, 1)

    Eq << Eq.initial.this.lhs.apply(algebra.sum.to.add.doit.outer)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.doit.inner)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.split({n})

    s = Symbol.s(Sum[j:0:n + 1](f[i] * g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, m))

    Eq << Eq[-2].this.rhs.split({n})

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.mul.to.sum)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[0].induct(reverse=True)

    Eq << algebra.eq.suffice.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
