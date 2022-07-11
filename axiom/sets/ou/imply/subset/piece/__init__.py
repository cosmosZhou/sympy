from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Subset(Piecewise(*expr_cond_pair(Subset, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B, S = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(etype=dtype.real * k)
    Eq << apply(Subset(f(x), S) & Element(x, A) | Subset(g(x), S) & Element(x, B - A) | Subset(h(x), S) & NotElement(x, A | B), wrt=S)

    Eq << Eq[0].this.args[1].args[1].apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.args[2].args[1].apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(sets.ou.imply.subset.piece.two, wrt=S)

    Eq << Eq[-1].apply(sets.ou.imply.subset.piece.two, wrt=S)


if __name__ == '__main__':
    run()

from . import two
# created on 2021-06-14
