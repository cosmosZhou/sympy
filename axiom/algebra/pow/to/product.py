from util import *


@apply
def apply(self):
    base, exp = self.of(Pow)
    fn, *limits = base.of(Product)
    assert exp >= 0 or exp.is_integer
    return Equal(self, Product(fn ** exp, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    f = Function.f(real=True)
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True, given=False, positive=True)
    t = Symbol.t(integer=True, nonnegative=True)

    Eq << apply(Product[k:n](f(k)) ** t)

    Eq << Eq[0].subs(n, 1)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.rhs.apply(algebra.product.to.mul.dissect, cond={n})

    Eq << Eq[-1].this.find(Product).apply(algebra.product.to.mul.dissect, cond={n})

    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.mul.split.base)

    Eq << Eq[0] * Eq[-1].find(Pow)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

