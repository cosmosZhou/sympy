from util import *


@apply
def apply(given):
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert _j == j
    n = n - 2
    return Equal(alpha(x[:n + 2]), alpha(x[:n], x[n] + 1 / x[n + 1]))


from axiom.discrete.imply.gt_zero.alpha import alpha


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)

    Eq << apply(All[i:1:n + 2](x[i] > 0))

    Eq << discrete.imply.infer.alpha.recurrence.apply(alpha(x[:n + 2]))

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-24
