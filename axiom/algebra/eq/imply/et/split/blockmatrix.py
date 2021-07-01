from util import *


@apply
def apply(given, indices):
    lhs, rhs = given.of(Equal)
    lhs = lhs.split(indices)
    rhs = rhs.split(indices)
    
    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)
    
    return Equal(lhs0, rhs0), Equal(lhs1, rhs1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n + 1,))
    y = Symbol.y(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]), slice(-1))

    

    Eq << Eq[0][:n]

    Eq << Eq[0][n]


if __name__ == '__main__':
    run()

