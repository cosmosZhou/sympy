from util import *


@apply
def apply(le):
    lhs, rhs = le.of(Expr >= BlockMatrix)

    args = []
    for e in rhs:
        assert len(lhs.shape) <= len(e.shape)
        args.append(lhs >= e)

    return tuple(args)


@prove
def prove(Eq):
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    a = Symbol(shape=(n,), real=True)
    b = Symbol(shape=(m,), real=True)
    x = Symbol(real=True)
    Eq << apply(x >= BlockMatrix(a, b))

    Eq << algebra.ge.imply.all.ge.apply(Eq[0])

    Eq << algebra.ge_piece.imply.ou.apply(Eq[-1])

    Eq << algebra.ou.imply.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.imply.all.single_variable.apply(Eq[-2], simplify=None), algebra.infer.imply.all.single_variable.apply(Eq[-1], simplify=None)

    Eq <<= algebra.all.imply.all.limits.restrict.apply(Eq[-2], domain=Range(0, n), simplify=None), algebra.all.imply.all.limits.restrict.apply(Eq[-1], domain=Range(n, m + n), simplify=None)

    Eq << algebra.all_ge.imply.ge.lamda.apply(Eq[-2])

    Eq << algebra.all_ge.imply.ge.lamda.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-04-01
