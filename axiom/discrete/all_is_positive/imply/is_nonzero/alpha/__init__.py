from util import *
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given):
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[0, Expr]])
    assert _j == j
    return Unequal(alpha(x[:n]), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:0:n](x[i] > 0))

    x_ = Symbol.x(real=True, positive=True, shape=(oo,))
    Eq << discrete.imply.is_nonzero.alpha.apply(x_[:n])

    Eq << Eq[-1].subs(x_[:n], x[:n])

    Eq << algebra.ou.imply.suffice.apply(Eq[-1], 1)

    Eq << Eq[-1].this.lhs.simplify()
    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

from . import offset
