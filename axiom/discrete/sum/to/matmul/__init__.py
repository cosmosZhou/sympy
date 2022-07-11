from util import *


@apply
def apply(self, *, simplify=True):
    (former, latter), *limits = self.of(Sum[Expr * Expr])

    former = Lamda(former, *limits)
    latter = Lamda(latter, *limits)
    if simplify:
        former = former.simplify()
        latter = latter.simplify()
    return Equal(self, former @ latter, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y, x = Symbol(shape=(n,), real=True)
    Eq << apply(Sum[i:n](y[i] * x[i]))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-18
from . import arithmetic_progression
