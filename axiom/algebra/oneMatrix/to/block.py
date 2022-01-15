from util import *


@apply
def apply(self, pivot):
    assert self.is_OneMatrix
    n, *shape = self.shape
    assert pivot < n and pivot > 0
    return Equal(self, BlockMatrix([OneMatrix(pivot, *shape), OneMatrix(n - pivot, *shape)]), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    m = 4
    n = 5
    Eq << apply(OneMatrix(4, 5), pivot=2)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    

    
    


if __name__ == '__main__':
    run()
# created on 2021-10-07
# updated on 2021-10-09