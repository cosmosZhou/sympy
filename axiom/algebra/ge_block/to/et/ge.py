from util import *


@apply(given=None)
def apply(le):
    lhs, rhs = le.of(Expr >= BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs >= e)

    return Equivalent(le, And(*args))


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x >= BlockMatrix(a, b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge_block.imply.et.ge)

    Eq << Eq[-1].this.lhs.apply(algebra.ge_block.given.et.ge)

    


if __name__ == '__main__':
    run()
# created on 2022-04-01
