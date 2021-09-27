from util import *


@apply
def apply(n, x1, x2):
    assert n >= 3
    k, i, j = Symbol(integer=True)    
    R = Lamda[j:n](x2 ** j)
    A = Lamda[j:n, i:n - 1]((j + 1) ** (i + 1) * x1 ** j)

    return Equal(Det([R, A]), x1 ** Binomial(n, 2) * (x2 - x1) ** n * Product[k:1:n](factorial(k)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(3, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(n, x1, x2)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[0], cond=Equal(x1, 0))

    Eq << Eq[-1].this.lhs.apply(discrete.is_nonzero.imply.eq.det_blockMatrix.to.mul.prod.vandermonde.two, n, x2)
    
    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.blockMatrix.pop_front)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.transpose.blockMatrix, 1)

    Eq << Eq[-1].this.find(Lamda[Tuple, Tuple])().expr.args[0].simplify()

    Eq << Eq[-1].this.find(Det).apply(discrete.det_blockMatrix.to.zero)


if __name__ == '__main__':
    run()