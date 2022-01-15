from util import *


@apply
def apply(self):
    (expr, (i, S[0], n)), *args = self.of(Determinant[Mul[Lamda]])
    rhs = Product[i:n](expr) * Det(Mul(*args))
    return Equal(self, rhs)


@prove(proved=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    X = Symbol(shape=(n, n), complex=True)
    a = Function(real=True)
    i = Symbol(integer=True)
    Eq << apply(Determinant(Lamda[i:n](a(i)) * X))

    


if __name__ == '__main__':
    run()
# created on 2022-01-15
