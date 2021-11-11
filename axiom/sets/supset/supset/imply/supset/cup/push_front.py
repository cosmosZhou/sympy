from util import *


@apply
def apply(*imply):
    from axiom.algebra.eq.eq.imply.eq.sum.push_front import absorb_front
    return absorb_front(Cup, Supset, *imply)


@prove
def prove(Eq):
    from axiom import sets
    k, a = Symbol(integer=True)
    b = Symbol(domain=Range(a + 1, oo))
    g, f = Function(etype=dtype.integer)

    Eq << apply(Supset(g(a - 1), f(a - 1)), Supset(Cup[k:a:b](g(k)), Cup[k:a:b](f(k))))

    Eq << sets.supset.supset.imply.supset.union.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()

# created on 2021-07-08
# updated on 2021-07-08
