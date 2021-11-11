from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.inner import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    n = 5
    Eq << apply(Product[j:n, i:m](x[i, j]))

    s = Symbol(Lamda[i](Product[j:n](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(algebra.prod.to.mul.doit)

    Eq << Eq[-2].subs(Eq[-1]).reversed


if __name__ == '__main__':
    run()

from . import setlimit
# created on 2020-03-05
# updated on 2020-03-05
