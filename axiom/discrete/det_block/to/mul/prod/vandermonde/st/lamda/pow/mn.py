from util import *


@apply
def apply(self):
    (((j, i), (x1, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[j], S[i]), ((x2, S[j]))), (S[j], S[0], S[m]), (S[i], S[0], S[m - d])) = self.of(Det[BlockMatrix[Lamda[Pow * Pow], Lamda[Pow * Pow]]])
    assert m > d + 1
    return Equal(self, x2 ** Binomial(m - d, 2) * x1 ** Binomial(d, 2) * (x2 - x1) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 2, oo))
    i, j = Symbol(integer=True)
    x1, x2 = Symbol(complex=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:m, i:d](j ** i * x1 ** j), Lamda[j:m, i:m - d](j ** i * x2 ** j)])))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(x2, 0))

    Eq << Eq[-1].this.lhs.apply(discrete.ne_zero.imply.eq.det_block.to.mul.prod.vandermonde.mn, x1, m, d)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.find(Lamda[2]).apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-1].this.find(BlockMatrix).args[1].find(Lamda[Tuple[2]])().expr.args[0].simplify()

    Eq << Eq[-1].this.find(Det).apply(discrete.det_block.to.zero)

    


if __name__ == '__main__':
    run()
# created on 2022-07-11
