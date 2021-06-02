from util import *


import axiom
from axiom.algebra.sum.doit.inner.setlimit import doit


@apply
def apply(self):
    assert self.is_Product
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)

    Eq << apply(Product[j:{0, 1, 2, 3}, i:m](x[i, j]))

    s = Symbol.s(Lamda[i](Product[j:{0, 1, 2, 3}](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.product.to.mul.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

