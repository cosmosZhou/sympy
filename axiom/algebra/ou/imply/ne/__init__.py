from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return Unequal(Piecewise(*expr_cond_pair(Unequal, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(shape=(k,), real=True)

    p = Symbol(shape=(k,), real=True, given=True)

    Eq << apply(Unequal(f(x), p) & Element(x, A) | Unequal(p, g(x)) & Element(x, B - A) | Unequal(p, h(x)) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.args[2].args[1].apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.ou.imply.ne.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.ne.two, wrt=p)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

from . import two
# created on 2020-02-08
