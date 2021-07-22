from util import *


@apply
def apply(self):
    A, B = self.of(MatMul)
    m, n = A.shape
    _n, l = B.shape
    assert n == _n
    
    prod = [[0] * l for i in range(m)]
    for i in range(m):
        for j in range(l):
            for k in range(n):
                prod[i][j] += A[i, k] * B[k, j]
        
        
    rhs = Matrix(prod)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    a0 = Symbol.a0(real=True)
    a1 = Symbol.a1(real=True)
    a2 = Symbol.a2(real=True)
    a3 = Symbol.a3(real=True)
    b0 = Symbol.b0(real=True)
    b1 = Symbol.b1(real=True)
    b2 = Symbol.b2(real=True)
    b3 = Symbol.b3(real=True)
    c0 = Symbol.c0(real=True)
    c1 = Symbol.c1(real=True)
    c2 = Symbol.c2(real=True)
    d0 = Symbol.d0(real=True)
    d1 = Symbol.d1(real=True)
    d2 = Symbol.d2(real=True)
    _a0 = Symbol("a0'", real=True)
    _a1 = Symbol("a1'", real=True)
    _b0 = Symbol("b0'", real=True)
    _b1 = Symbol("b1'", real=True)
    _c0 = Symbol("c0'", real=True)
    _c1 = Symbol("c1'", real=True)
    X = Matrix([[a0, a1, a2], [b0, b1, b2], [c0, c1, c2], [d0, d1, d2]])
    Y = Matrix([[_a0, _a1], [_b0, _b1], [_c0, _c1]])
    Eq << apply(MatMul(X, Y))

    X = Symbol.X(X)
    Y = Symbol.Y(Y)
    Eq << X.this.definition

    Eq << Y.this.definition
    Eq << Eq[1] @ Y

    

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[0].subs(Eq[1].reversed)
    Eq << Eq[-1].subs(Eq[2].reversed)


if __name__ == '__main__':
    run()