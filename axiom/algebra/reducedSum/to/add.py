from util import *


@apply
def apply(self):
    args = self.of(ReducedSum[Add])
    len_shape = len(self.shape)
    new_args = []
    for arg in args:
        if len(arg.shape) >= len_shape:
            new_args.append(ReducedSum(arg).simplify())
        else:
            new_args.append(arg)
    return Equal(self, Add(*new_args), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    Eq << apply(ReducedSum(x + y))

    Eq << Eq[0].this.lhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.reducedSum)

    


if __name__ == '__main__':
    run()
# created on 2022-04-02
