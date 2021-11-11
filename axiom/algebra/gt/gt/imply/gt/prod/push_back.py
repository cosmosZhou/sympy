from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push_back import absorb_back
    return absorb_back(Product, Greater, *imply, criteria=lambda cond: cond.rhs > 0)


@prove
def prove(Eq):
    from axiom import algebra

    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g = Function(integer=True)
    f = Function(integer=True, positive=True)
    Eq << apply((g(b) > f(b)), Product[k:a:b](g(k)) > Product[k:a:b](f(k)))

    Eq << algebra.gt.gt.imply.gt.mul.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.apply(algebra.prod.to.mul.split, cond={b})

    Eq << Eq[-1].this.rhs.apply(algebra.prod.to.mul.split, cond={b})


if __name__ == '__main__':
    run()

# created on 2019-01-19
# updated on 2019-01-19
