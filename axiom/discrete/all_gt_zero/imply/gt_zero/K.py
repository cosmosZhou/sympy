from util import *


@apply
def apply(given):
    from axiom.discrete.K.to.add.definition import K
    (x, _j), (j, n) = given.of(All[Indexed > 0, Tuple[1, Expr]])
    assert _j == j
    return Greater(K(x[:n]), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(real=True, shape=(oo,))
    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    Eq << apply(All[i:1:n](x[i] > 0))

    Eq << discrete.imply.infer.gt_zero.K.apply(x[:n])

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-15
# updated on 2020-09-15
