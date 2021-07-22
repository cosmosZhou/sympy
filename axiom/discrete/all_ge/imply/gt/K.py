from util import *
from axiom.discrete.K.to.add.definition import K


@apply
def apply(given):
    (x, _j), (j, n1) = given.of(All[Indexed >= 1, Tuple[1, Expr]])

    n = n1 - 1
    assert _j == j
    assert n >= 2
    return Greater(K(x[:n + 1]), K(x[:n]))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol.x(real=True, shape=(oo,))
    i = Symbol.i(integer=True)
    n = Symbol.n(domain=Range(2, oo))

    Eq << apply(All[i:1:n + 1](x[i] >= 1))

    Eq << Eq[-1].this.find(K).defun()

    Eq << algebra.all.imply.all.split.apply(Eq[0], cond={n})

    Eq << Eq[-1].this.expr.apply(algebra.ge.imply.is_positive)

    Eq << discrete.all_is_positive.imply.is_positive.K.apply(Eq[-1])

    Eq << algebra.is_positive.ge.imply.ge.mul.apply(Eq[-1], Eq[-4])

    Eq << algebra.all.imply.all.split.apply(Eq[-3], cond={n - 1})

    Eq << discrete.all_is_positive.imply.is_positive.K.apply(Eq[-1])

    Eq << algebra.gt.ge.imply.gt.add.apply(Eq[-1], Eq[-4])


if __name__ == '__main__':
    run()

