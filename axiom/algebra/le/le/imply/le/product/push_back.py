from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push_back import absorb_back
    return absorb_back(Product, LessEqual, *imply, criteria=lambda cond: cond.lhs >= 0)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True, nonnegative=True)
    f = Function.f(integer=True)
    Eq << apply((g(b) <= f(b)), Product[k:a:b](g(k)) <= Product[k:a:b](f(k)))

    Eq << algebra.le.le.imply.le.multiply.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(algebra.product.to.mul.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(algebra.product.to.mul.split, cond={b})


if __name__ == '__main__':
    run()

