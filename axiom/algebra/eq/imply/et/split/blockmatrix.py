from util import *


@apply
def apply(given, indices):
    lhs, rhs = given.of(Equal)
    lhs = lhs.split(indices)
    rhs = rhs.split(indices)
    assert lhs.is_BlockMatrix and rhs.is_BlockMatrix
    return And(*[Equal(lhs, rhs) for lhs, rhs in zip(lhs.args, rhs.args)])


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n + 1,))
    y = Symbol.y(real=True, shape=(oo,))
    Eq << apply(Equal(x, y[:n + 1]), Slice[-1:])

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[0][:n]

    Eq << Eq[0][n]


if __name__ == '__main__':
    run()

