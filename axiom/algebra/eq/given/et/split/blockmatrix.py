from util import *


@apply
def apply(given, indices=None):
    lhs, rhs = given.of(Equal)
    if indices is None:
        indices = slice(-1)

    lhs = lhs.split(indices)
    rhs = rhs.split(indices)
    
    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)
    
    first = Equal(lhs0, rhs0)
    second = Equal(lhs1, rhs1)
    
    return first, second


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n + 1,))
    y = Symbol.y(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]), slice(-1))

    Eq << Eq[-2] @ BlockMatrix([Identity(n), ZeroMatrix(n)]).T

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << BlockMatrix(ZeroMatrix(n), x[n]).this.subs(Eq[2])

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()

