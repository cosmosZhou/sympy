from util import *


@apply
def apply(given, indices=None):
    lhs, rhs = given.of(Equal)
    if indices is None:
        indices = Slice[-1:]

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

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << Eq[-2] @ BlockMatrix([Identity(n), ZeroMatrix(n)]).T

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << BlockMatrix(ZeroMatrix(n), x[n]).this.subs(Eq[3])

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()

