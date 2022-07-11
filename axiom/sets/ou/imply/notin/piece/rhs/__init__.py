from util import *


@apply
def apply(given, wrt=None):
    from axiom.sets.ou.imply.el.piece.two import expr_cond_pair
    or_eqs = given.of(Or)

    return NotElement(wrt, Piecewise(*expr_cond_pair(NotElement, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, shape=(k,), given=True)
    A, B = Symbol(etype=dtype.real * k, given=True)
    f, g, h = Function(etype=dtype.real * (k,))
    Eq << apply(NotElement(y, f(x)) & Element(x, A) | NotElement(y, g(x)) & Element(x, B - A) | NotElement(y, h(x)) & NotElement(x, A | B), wrt=y)

    Eq << Eq[0].this.args[1].args[0].apply(sets.el_complement.imply.et, simplify=None)

    Eq << Eq[-1].this.args[2].args[0].apply(sets.notin.imply.et.split.union, simplify=None)

    Eq << Eq[-1].apply(algebra.ou.imply.ou.collect, cond=NotElement(x, A))

    Eq << Eq[-1].this.args[0].args[0].apply(sets.ou.imply.notin.piece.rhs.two, wrt=y)

    Eq << Eq[-1].apply(sets.ou.imply.notin.piece.rhs.two, wrt=y)


if __name__ == '__main__':
    run()
from . import two
# created on 2021-06-10
