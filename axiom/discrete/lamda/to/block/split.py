from util import *


@apply
def apply(self, pivot):
    expr, *limits, (i, _0, n) = self.of(Lamda)
    assert _0 == 0
    args = []
    assert n > pivot > 0
    first = Lamda(expr, *limits, (i, 0, pivot)).simplify()
    second = Lamda(expr, *limits, (i, pivot, n)).simplify()
    return Equal(self, BlockMatrix([first, second]))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(positive=True, integer=True, given=False)
    m = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Lamda[j:n, i:m](f(i, j)), 1)

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.kroneckerDelta)





if __name__ == '__main__':
    run()
# created on 2021-10-04
