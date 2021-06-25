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
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)
    Eq << apply(Sum[i:0:n, j:0:n](f[j] * g[i, j]))

    Eq << Eq[-1].this.rhs.function.apply(algebra.mul.to.sum)


if __name__ == '__main__':
    run()

