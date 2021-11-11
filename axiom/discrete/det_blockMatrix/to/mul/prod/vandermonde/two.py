from util import *


@apply
def apply(n, x1, x2):
    assert n >= 1
    i, j = Symbol(integer=True)
    return Equal(Det([Lamda[j:n + 1](x2 ** j), Lamda[j:n + 1, i:n](j ** i * x1 ** j)]), x1 ** Binomial(n, 2) * (x1 - x2) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(3, oo))
    x1, x2 = Symbol(complex=True)
    Eq << apply(n, x1, x2)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(x1, 0))

    Eq << Eq[-1].this.lhs.apply(discrete.ne_zero.imply.eq.det_blockMatrix.to.mul.prod.vandermonde.two, n, x2)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.blockMatrix.pop_front)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.transpose.blockMatrix, 1)

    Eq << Eq[-1].this.find(Lamda[Tuple, Tuple])().expr.args[0].simplify()

    Eq << Eq[-1].this.find(Det).apply(discrete.det_blockMatrix.to.zero)

    
    


if __name__ == '__main__':
    run()
# created on 2020-10-15
# updated on 2021-10-04