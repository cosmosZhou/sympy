from util import *


@apply
def apply(self, k):
    assert self.is_ZeroMatrix
    m, *shape = self.shape
    
    assert k <= m and k >= 0
        
    A = ZeroMatrix(k, *shape)
    B = ZeroMatrix(m - k, *shape)
    return Equal(self, BlockMatrix(A, B), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m = 5
    n = 6
    k = 2
    Eq << apply(ZeroMatrix(m, n), k)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)





if __name__ == '__main__':
    run()
# created on 2021-11-22
