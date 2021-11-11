from util import *


@apply
def apply(self):
    args = self.of(Determinant[Mul])
    scalar = []
    matrix = []
    for arg in args:
        if arg.shape:
            matrix.append(arg)
        else:
            scalar.append(arg)
    scalar = Mul(*scalar)
    matrix = Mul(*matrix)

    n = matrix.shape[-1]
    return Equal(self, scalar ** n * Det(matrix))


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    X = Symbol(shape=(n, n), complex=True)
    a = Symbol(complex=True)
    Eq << apply(Determinant(a * X))




if __name__ == '__main__':
    run()
# created on 2020-08-19
# updated on 2020-08-19
