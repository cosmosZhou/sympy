from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.push_front import absorb
    return Equal(self, absorb(Product, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(integer=True)
    Eq << apply(Mul(Product[k:1 + i:n](f(k)), f(i)))

    Eq << Eq[-1].this.rhs.apply(algebra.product.to.mul.split, cond={i})


if __name__ == '__main__':
    run()
