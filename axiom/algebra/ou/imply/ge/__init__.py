from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return GreaterEqual(Piecewise(*expr_cond_pair(GreaterEqual, or_eqs, wrt)).simplify(), wrt)


@prove
def prove(Eq):
    from axiom import sets, algebra
    k = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(shape=(k,), real=True)

    p = Symbol(shape=(k,), real=True, given=True)

    Eq << apply(GreaterEqual(f(x), p) & Element(x, A) | GreaterEqual(g(x), p) & Element(x, B - A) | GreaterEqual(h(x), p) & NotElement(x, A | B), wrt=p)

    Eq << Eq[0].this.args[1].args[1].apply(sets.el.imply.et.split.complement, simplify=None)

    Eq << Eq[-1].this.args[2].args[1].apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(algebra.ou.imply.ge.two, wrt=p)

    Eq << Eq[-1].apply(algebra.ou.imply.ge.two, wrt=p)


if __name__ == '__main__':
    run()

from . import two
