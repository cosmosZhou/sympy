from util import *


@apply
def apply(self):
    function, limit, *limits = self.of(Sum)

    assert limit[0].is_integer

    rhs = ReducedSum(Lamda(self.expr, limit).simplify())
    if limits:
        rhs = Sum(rhs, *limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y = Symbol(shape=(n, n), real=True)
    Eq << apply(Sum[i:n, j:n](y[j, i]))
    Eq << Eq[-1].this.rhs.expr.apply(algebra.reducedSum.to.sum)


if __name__ == '__main__':
    run()
