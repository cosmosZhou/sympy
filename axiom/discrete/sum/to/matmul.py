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

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    y = Symbol.y(shape=(n,), real=True)
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(Sum[i:n](y[i] * x[i]))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()