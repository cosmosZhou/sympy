from util import *


@apply
def apply(self, var=None):
    A, B = self.of(MatMul)
    kwargs = {'var': var, 'generator': self}

    from axiom.discrete.matmul.to.lamda import generate_k_limit
    assert len(A.shape) == 1
    assert len(B.shape) == 1
    k_limit = generate_k_limit(A, B, **kwargs)
    k, *_ = k_limit
    rhs = Sum(A[k] * B[k], k_limit).simplify()
    return Equal(self, rhs, evaluate=False)


@prove(provable=False)
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n,), complex=True)
    Eq << apply(A @ B)


if __name__ == '__main__':
    run()
# created on 2019-11-09
