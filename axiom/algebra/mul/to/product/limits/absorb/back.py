from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.absorb.back import absorb
    return Equal(self, absorb(Product, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    i = Symbol.i(domain=Range(0, n + 1))
    f = Function.f(integer=True)
    Eq << apply(Mul(Product[k:i:n](f(k)), f(n)))

    Eq << Eq[-1].this.rhs.apply(algebra.product.to.mul.split, cond={n})

    # Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)

    # Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)
    return
    Eq << Eq[-1].this.rhs.args[0].apply(algebra.product.to.mul.doit.setlimit)


if __name__ == '__main__':
    run()
