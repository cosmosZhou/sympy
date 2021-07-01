from util import *
from axiom.discrete.imply.is_positive.alpha import alpha
from axiom.discrete.H.to.add.definition import H
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[0, Expr]])
    offset = _j - j
    if offset != 0:
        assert not offset._has(j)
        x = x[offset:]

    n = n - 1
    assert n > 0
    return Equal(K(x[1:n + 1]) / H(x[1:n + 1]), H(x[:n + 1]) / K(x[:n + 1]) - x[0])


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    Eq << apply(All[i:0:n + 1](x[i] > 0))

    x_ = Symbol.x(real=True, positive=True, shape=(oo,))
    Eq << discrete.continued_fraction.HK.KH.apply(x_[:n + 1])

    Eq << Eq[-1].subs(x_[:n + 1], x[:n + 1])

    Eq << algebra.all.imply.suffice.apply(Eq[-1])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

