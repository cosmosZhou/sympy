from util import *


@apply
def apply(self):
    args = self.of(Determinant[Mul])
    scalar = []    
    for arg in args:
        if arg.shape:
            n = arg.shape[-1]
            assert arg.is_Identity
        else:
            scalar.append(arg)
    scalar = Mul(*scalar)

    return Equal(self, scalar ** n)


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(complex=True)
    Eq << apply(Determinant(a * Identity(n)))


if __name__ == '__main__':
    run()