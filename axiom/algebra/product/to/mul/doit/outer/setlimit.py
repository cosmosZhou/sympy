from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit.outer.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    f = Function.f(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Product[j:f(i), i:finiteset](x[i, j]))

    s = Symbol.s(Lamda[i](Product[j:f(i)](x[i, j])))

    Eq << s[i].this.definition

    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, finiteset))

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.rhs.apply(algebra.product.to.mul.doit.setlimit)

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition

    Eq << Eq[-1].this.rhs.find(Indexed).definition


if __name__ == '__main__':
    run()

