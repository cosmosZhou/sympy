from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.absorb.back import absorb_back
    return absorb_back(Sum, LessEqual, *imply)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(integer=True)
    f = Function.f(integer=True)

    Eq << apply((g(b) <= f(b)), Sum[k:a:b](g(k)) <= Sum[k:a:b](f(k)))

    Eq << algebra.le.le.imply.le.add.apply(Eq[0], Eq[1])

    Eq << Eq[2].this.lhs.split({b})

    Eq << Eq[-1].this.rhs.split({b})


if __name__ == '__main__':
    run()

