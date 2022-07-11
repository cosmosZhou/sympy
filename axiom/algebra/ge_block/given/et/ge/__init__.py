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
    
    Eq << algebra.ge.given.all.ge.apply(Eq[0])
    
    Eq << algebra.ge_piece.given.ou.apply(Eq[-1])
    
    Eq << algebra.ge.imply.all.ge.apply(Eq[1])
    
    i = Eq[-1].rhs.index
    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, Range(-oo, n)), simplify=None)
    
    Eq.infer_lt = algebra.all.imply.infer.apply(Eq[-1])
    
    
    Eq << algebra.ge.imply.all.ge.apply(Eq[2])
    Eq << Eq[-1].subs(i, i - n)
    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, Range(n, oo)), simplify=None)
    Eq << algebra.all.imply.infer.apply(Eq[-1])
    Eq << algebra.infer.infer.imply.ou.apply(Eq.infer_lt, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2022-04-01
