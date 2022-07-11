from util import *


@apply(given=None)
def apply(le):
    lhs, rhs = le.of(BlockMatrix > Expr)

    args = []
    for e in lhs:
        assert len(rhs.shape) <= len(e.shape)
        args.append(e > rhs)

    return Equivalent(le, And(*args))


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(BlockMatrix(a, b) > x)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.block_gt.imply.et.gt)

    Eq << Eq[-1].this.lhs.apply(algebra.block_gt.given.et.gt)

    


if __name__ == '__main__':
    run()
# created on 2022-04-01
