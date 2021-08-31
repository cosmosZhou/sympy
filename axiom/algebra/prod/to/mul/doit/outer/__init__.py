from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit.outer import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    f = Function(integer=True)

    n = 5
    Eq << apply(Product[j:f(i), i:n](x[i, j]))

    s = Symbol(Lamda[i](Product[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(algebra.prod.to.mul.doit).reversed

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

from . import setlimit
