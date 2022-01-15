from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.push_back import absorb
    return Equal(self, absorb(Product, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k, n = Symbol(integer=True)
    i = Symbol(domain=Range(n + 1))
    f = Function(integer=True)
    Eq << apply(Mul(Product[k:i:n](f(k)), f(n)))

    Eq << Eq[-1].this.rhs.apply(algebra.prod.to.mul.split, cond={n})

    # Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)

    # Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)


if __name__ == '__main__':
    run()
# created on 2020-02-01
