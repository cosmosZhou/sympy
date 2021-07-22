from util import *


@apply
def apply(self):
    function, i_limit, j_limit = self.of(Product)
    j, *_ = j_limit
    assert not i_limit._has(j)
    return Equal(self, Product(function, j_limit, i_limit))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    Eq << apply(Product[i:0:m, j:0:n](f[i] + g[i, j]))

    #Eq.initial = Eq[0].subs(n, 1)
    #
    #Eq << Eq.initial.this.lhs.apply(algebra.product.doit.outer)
    #
    #Eq << Eq[-1].this.rhs.apply(algebra.product.doit.inner)
    #
    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(algebra.product.to.mul.split, cond={n})

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.product.to.mul.doit.outer.setlimit)

    s = Symbol.s(Product[j:0:n + 1](f[i] + g[i, j]))
    Eq << s.this.definition

    Eq << Eq[-1].apply(algebra.eq.imply.eq.product, (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.product.to.mul.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.product.to.mul)

    Eq << Eq[2].subs(Eq[-1].reversed)

    Eq << Eq[0] * Eq[-1].lhs.args[0]

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

from . import intlimit
from . import subs
