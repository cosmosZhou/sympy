from util import *


def matrix_to_tuple(self):
    if not self.shape:
        return self
    n = self.shape[-1]
    n = int(n)
    return tuple(matrix_to_tuple(self[i]) for i in range(n))

@apply
def apply(self):
    assert self.shape
    rhs = Matrix(matrix_to_tuple(self))
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(shape=(4, 4), real=True)
    Eq << apply(x)

    Eq << Eq[0].this.lhs.apply(algebra.expr.to.lamda)

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.matrix)

    


if __name__ == '__main__':
    run()
# created on 2022-01-12
