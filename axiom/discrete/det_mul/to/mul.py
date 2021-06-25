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


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol.n(integer=True, positive=True)
    X = Symbol.X(shape=(n, n), complex=True)
    a = Symbol.a(complex=True)
    Eq << apply(Determinant(a * X))

    A = Symbol.A(a * Identity(n))
    Eq << A.this.definition

    Eq << Eq[-1] @ X

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.args[0].arg.definition

    Eq << Eq[-1].this.lhs.find(Det[Mul]).apply(discrete.det_mul.to.pow)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()