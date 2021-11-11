from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True, positive=True)
    n = 5
    x = Symbol(real=True, shape=(n, k))
    i = Symbol(integer=True)
    Eq << apply(Product[i](x[i]))

    Eq << Eq[-1].this.lhs.apply(algebra.prod.limits.domain_defined.insert)

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.split, cond={n})

    n -= 1
    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.split, cond={n})


if __name__ == '__main__':
    run()

from . import outer
from . import setlimit
# created on 2020-03-04
# updated on 2020-03-04
