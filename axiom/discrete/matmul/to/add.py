from util import *


def convert(self):
    for i, arg in enumerate(self.of(MatMul)):
        if arg.is_Add:
            args = [*self.args]
            if i > 0:
                left = Add(*(self.func(*args[:i]) @ a for a in arg.args))
                right = args[i + 1:]
                if right:
                    return left @ self.func(*right)
                else:
                    return left

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
