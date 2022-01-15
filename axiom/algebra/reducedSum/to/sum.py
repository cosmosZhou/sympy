from util import *


@apply
def apply(self, i=None):
    if i is None:
        i = self.arg.generate_var(integer=True)

    n = self.arg.shape[-1]
    rhs = Sum[i:n](self.arg[i])

    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    y = Symbol(shape=(n,), real=True)
    Eq << apply(ReducedSum(y))


if __name__ == '__main__':
    run()
# created on 2019-11-10
