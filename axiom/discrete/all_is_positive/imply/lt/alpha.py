from util import *
from axiom.discrete.K.to.add.definition import K
from axiom.discrete.imply.is_positive.alpha import alpha


@apply
def apply(given, n):
    (x, _j), j = given.of(All[Indexed > 0, Tuple[1, oo]])
    assert _j == j
    assert n > 0
    return Less(alpha(x[:2 * n - 1]), alpha(x[:2 * n + 1]))


@prove(proved=False)
def prove(Eq):
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:oo](x[i] > 0), n)
    return
    Eq << discrete.imply.suffice.is_positive.K.apply(x[:n])

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

