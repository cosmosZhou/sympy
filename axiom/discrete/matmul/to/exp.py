from util import *


@apply
def apply(self):
    A, B = self.of(Exp @ Exp)
    if len(A.shape) < len(B.shape):
        rhs = ReducedSum(exp(A + B.T))
    elif len(A.shape) > len(B.shape):
        rhs = ReducedSum(exp(A + B))
    else:
        return
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    A = Symbol.A(shape=(k, m), complex=True)
    B = Symbol.B(shape=(m,), complex=True)
    
    #A = Symbol.A(shape=(m,), complex=True)
    #B = Symbol.B(shape=(m, n), complex=True)
    Eq << apply(exp(A) @ exp(B))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.lamda, var=Eq[1].lhs.function.variable)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.function.apply(algebra.exp.to.mul)


if __name__ == '__main__':
    run()