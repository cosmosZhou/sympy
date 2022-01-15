from util import *


def convert(self):
    for i, arg in enumerate(self.of(MatMul)):
        if arg.is_Add:
            args = [*self.args]
            if i > 0:
                former, latter = self.func(*args[:i]), args[i + 1:]
                left = Add(*(former @ a for a in arg.args))
                if latter:
                    left @= self.func(*latter)
                return left
            else:
                latter = self.func(*args[1:])
                return Add(*(a @ latter for a in arg.args))

@apply
def apply(self):
    rhs = convert(self)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    x, a, b = Symbol(shape=(n, n), complex=True)
    Eq << apply(x @ (a + b))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)


if __name__ == '__main__':
    run()

# created on 2020-11-10

from . import st
