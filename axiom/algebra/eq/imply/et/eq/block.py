from util import *


@apply
def apply(given, index=-1):
    lhs, rhs = given.of(Equal)
    from axiom.algebra.sum.to.add.split import split
    from axiom.algebra.symbol.to.block import symbol_split
    if lhs.is_symbol:
        lhs = symbol_split(lhs, slice(0, index))
    elif lhs.is_Lamda:
        lhs = split(Lamda, lhs, slice(0, index))
    else:
        return

    if rhs.is_symbol:
        rhs = symbol_split(rhs, slice(0, index))
    elif rhs.is_Lamda:
        rhs = split(Lamda, rhs, slice(0, index))

    lhs0, lhs1 = lhs.of(BlockMatrix)
    rhs0, rhs1 = rhs.of(BlockMatrix)

    return Equal(lhs0, rhs0), Equal(lhs1, rhs1)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n + 1,))
    y = Symbol(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]))

    Eq << Eq[0][:n]

    Eq << Eq[0][n]


if __name__ == '__main__':
    run()


# created on 2019-05-01
