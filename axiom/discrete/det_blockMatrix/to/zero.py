from util import *


def is_square(A):
    if len(A.shape) == 2:
        m, n = A.shape
        return m == n
    
@apply
def apply(self):
    def is_valid(A, B):
        if A.is_ZeroMatrix and is_square(A):
            if len(B.shape) < 2:
                n = 1
            else:
                n = B.shape[0]
            return A.shape[0] > n
        
    AB, CD = self.of(Determinant[BlockMatrix])
    if AB.is_BlockMatrix:
        A, B = AB.args
    else:
        A, B = AB.of(Transpose[BlockMatrix])
        
    if CD.is_BlockMatrix:
        C, D = CD.args            
    else:
        C, D = CD.of(Transpose[BlockMatrix])
        
    assert is_valid(A, B) or is_valid(B, A) or is_valid(C, D) or is_valid(D, C)
    return Equal(self, 0)


@prove(proved=False)
def prove(Eq):
    m = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(1, m))
    A = Symbol(complex=True, shape=(n, n))
    B = Symbol(complex=True, shape=(n, m))
    C = Symbol(complex=True, shape=(m, n))
    Eq << apply(Determinant(BlockMatrix([[A, B],[C, ZeroMatrix(m, m)]])))


if __name__ == '__main__':
    run()