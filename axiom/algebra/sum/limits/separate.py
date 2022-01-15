from util import *


@apply
def apply(sgm):
    function, *limits = sgm.of(Sum)
    assert len(limits) > 1
    limit, *limits = limits

    function = sgm.func(function, limit).simplify()

    return Equal(sgm, sgm.func(function, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:0:n, j:0:n](f[j] * g[i, j]))

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.sum)


if __name__ == '__main__':
    run()

# created on 2019-11-11
