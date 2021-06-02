from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.absorb.back import absorb_back
    return absorb_back(Product, Greater, *imply, criteria=lambda cond: cond.rhs > 0)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True)
    f = Function.f(integer=True, positive=True)

    Eq << apply((g(b) > f(b)), Product[k:a:b](g(k)) > Product[k:a:b](f(k)))

    Eq << algebra.gt.gt.imply.gt.multiply.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.split({b})

    Eq << Eq[-1].this.rhs.split({b})


if __name__ == '__main__':
    run()
