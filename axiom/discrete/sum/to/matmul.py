from util import *


@apply
def apply(self):
    (first, second), *limits = self.of(Sum[Expr * Expr])
    if self.limits:
        rhs = Lamda(first, *limits).simplify() @ Lamda(second, *limits).simplify()
    else:
        rhs = first @ second

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y, x = Symbol(shape=(n,), real=True)
    Eq << apply(Sum[i:n](y[i] * x[i]))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
