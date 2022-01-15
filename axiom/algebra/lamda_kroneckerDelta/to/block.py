from util import *


@apply
def apply(self):
    (c, hj), (j, S[0], n) = self.of(Lamda[KroneckerDelta])
    if c._has(j): 
        c, hj = hj, c
        
    b, a = hj.of_simple_poly(j)
    #a * j + b = c
    if a == 1:
        i = c - b
    elif a == -1:
        i = b - c
        
    if i == n - 1:
        rhs = BlockMatrix(ZeroMatrix(n - 1), 1)
    elif i == 0:
        rhs = BlockMatrix(1, ZeroMatrix(n - 1))
    else:
        assert n - i
        rhs = BlockMatrix(ZeroMatrix(i), 1, ZeroMatrix(n - i - 1))

    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Lamda[j:n](KroneckerDelta(n - 1, j)))

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.kroneckerDelta)

    


if __name__ == '__main__':
    run()
# created on 2021-12-30
# updated on 2022-01-04