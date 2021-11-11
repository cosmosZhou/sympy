from util import *


@apply
def apply(given):
    from axiom.algebra.eq_piece.imply.ou import piecewise_to_ou
    return piecewise_to_ou(Supset, given)


@prove
def prove(Eq):
    from axiom import sets

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, p = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(etype=dtype.real * (k,))
    Eq << apply(Supset(p, Piecewise((f(x), Element(x, A)), (g(x), Element(x, B)), (h(x), True))))

    Eq << Eq[-1].this.find(Supset).reversed

    Eq << Eq[-1].this.find(Supset).reversed

    Eq << Eq[-1].this.find(Supset).reversed

    Eq << sets.ou.imply.subset.piece.apply(Eq[-1], wrt=p).reversed


if __name__ == '__main__':
    run()
# created on 2021-07-10
# updated on 2021-07-10
