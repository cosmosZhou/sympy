from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), ((((S[A], S[i]), (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u)]), (S[i + n - Min(n, u)], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Lamda[
                BlockMatrix[
                    NegativeInfinity * OneMatrix,
                    Sliced[Indexed]
                ],
                Tuple[Min]
                ],
            Lamda
            ],
        BlockMatrix[
            Lamda[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix
                    ],
                Tuple[Min]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and l >= 2 and u >= 2
    return Infer(i < Min(l, n, n - Min(u, n)), Equal(z[i], BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:]))), \
        Infer(Element(i, Range(n - Min(u, n), Min(l, n))), Equal(z[i], BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:n + Min(l, n) - i - 1], -oo * OneMatrix(Min(u, n) + i - n)))), \
        Infer(i >= Max(Min(l, n), n - Min(u, n)), Equal(z[i], BlockMatrix(z[i,:n + Min(l, n) - i - 1], -oo * OneMatrix(Min(u, n) + i - n)))), \



@prove
def prove(Eq):
    from axiom import algebra

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n)](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i,:i])),
            Lamda[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])),
        BlockMatrix(
        Lamda[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
        Lamda[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * OneMatrix(i))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << algebra.infer.given.all.apply(Eq[1])

    Eq.block1 = algebra.all.given.all.limits.domain_defined.apply(Eq[-1])

    Eq.block2 = algebra.infer.given.all.apply(Eq[2])

    Eq << algebra.infer.given.all.apply(Eq[3])

    Eq.block3 = algebra.all.given.all.limits.domain_defined.apply(Eq[-1])

    j = Symbol(integer=True)
    Eq <<= Eq.block1.this.expr.lhs.apply(algebra.expr.to.lamda, j)

    Eq <<= Eq[-1].this.expr.rhs.apply(algebra.expr.to.lamda, j)

    Eq.z_ij_def = Eq[0][i][j]

    Eq << Eq[-1].subs(Eq.z_ij_def)

    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.to.add, Eq[-1].find(logsumexp))


    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()


    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()
    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()
    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()
    Eq << Eq[-1].this.expr.lhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this(i).find(And).simplify()
    Eq <<= Eq.block2.this.expr.lhs.apply(algebra.expr.to.lamda, j)
    Eq <<= Eq[-1].this.expr.rhs.apply(algebra.expr.to.lamda, j)
    Eq <<= Eq[-1].this.find(ExprCondPair[2]).cond.apply(algebra.lt.transport, rhs=slice(0, 4, 3))
    Eq << Eq[-1].subs(Eq.z_ij_def)
    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.to.add, Eq[-1].find(logsumexp))
    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()
    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()
    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()
    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()
    Eq << Eq[-1].this.expr.lhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this(i).find(And).simplify()
    Eq << Eq[-1].this.find(Less[2]).apply(algebra.lt.transport, rhs=slice(0, 2))
    Eq << Eq[-1].this.find(Or).apply(algebra.ou_lt.to.lt.max)
    Eq << Eq[-1].this().find(Max).simplify()
    Eq <<= Eq.block3.this.expr.lhs.apply(algebra.expr.to.lamda, j)
    Eq <<= Eq[-1].this.expr.rhs.apply(algebra.expr.to.lamda, j)
    Eq <<= Eq[-1].this.find(Less).apply(algebra.lt.transport, rhs=slice(0, 4, 3))
    Eq << Eq[-1].subs(Eq.z_ij_def)
    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.to.add, Eq[-1].find(logsumexp))
    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Min).simplify()
    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Min).simplify()
    Eq << Eq[-1].this(i).expr.lhs.find(Symbol < Symbol - Min).simplify()
    Eq << Eq[-1].this(i).expr.rhs.find(Symbol < Symbol - Min).simplify()
    #Eq << Eq[-1].this.expr.lhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this.expr.rhs.apply(algebra.piece.flatten)
    Eq << Eq[-1].this.find(And[Or]).simplify()
    Eq << Eq[-1].this.find(Less[2]).apply(algebra.lt.transport, rhs=slice(0, 2))
    Eq << Eq[-1].this.find(Or).apply(algebra.ou_lt.to.lt.max)
    Eq << Eq[-1].this(i).find(Max).simplify()




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2022-01-08
from . import tf
