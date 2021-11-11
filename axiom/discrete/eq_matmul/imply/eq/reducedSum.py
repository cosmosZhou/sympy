from util import *


@apply
def apply(given):
    (x, w), y = given.of(Equal[MatMul])
    [n] = x.shape
    _n, i, j = w.of(SwapMatrix)
    assert n == _n
    assert i >= 0 and i < n
    assert j >= 0 and j < n
    return Equal(ReducedSum(x), ReducedSum(y))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y))

    t = Symbol(integer=True)
    Eq << Eq[0][t].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[1].this.rhs.apply(algebra.reducedSum.to.sum, t)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum, t)

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2019-11-10
# updated on 2019-11-10
