from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push_back import absorb_back
    return absorb_back(Cup, Supset, *imply)


@prove
def prove(Eq):
    from axiom import sets
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Range(a + 1, oo))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Supset(g(b), f(b)), Supset(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << sets.supset.supset.imply.supset.union.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

