from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    n = 5
    x = Symbol.x(real=True, shape=(n, k))
    i = Symbol.i(integer=True)

    Eq << apply(Product[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(algebra.product.limits.domain_defined.insert)

    n -= 1
    Eq << Eq[-1].this.lhs.split({n})

    n -= 1
    Eq << Eq[-1].this.find(Product).split({n})

    n -= 1
    Eq << Eq[-1].this.find(Product).split({n})

    n -= 1
    Eq << Eq[-1].this.find(Product).split({n})


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
