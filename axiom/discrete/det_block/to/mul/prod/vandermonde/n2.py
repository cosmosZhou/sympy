from util import *


@apply
def apply(self):
    ((x1, j), j_limit), ((S[j], (S[x1], S[j])), S[j_limit]), (((S[j], i), (x2, S[j])), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Lamda[Pow], Lamda[Symbol * Pow], Lamda[Pow * Pow]]])

    S[j], S[0], S[n + 2:n >= 1] = j_limit

    return Equal(self, x1 * x2 ** Binomial(n, 2) * (x2 - x1) ** (2 * n) * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(2, oo))
    x1, x2 = Symbol(complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det([Lamda[j:n + 2](x1 ** j), Lamda[j:n + 2](j * x1 ** j), Lamda[j:n + 2, i:n](j ** i * x2 ** j)]))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(x2, 0))

    Eq << Eq[-1].this.lhs.apply(discrete.ne_zero.imply.eq.det_block.to.mul.prod.vandermonde.n2, n, x1)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.find(Lamda[2]).apply(algebra.lamda.to.block.pop_front)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.block.pop_front)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-1].this.find(Lamda[Tuple[2]])().expr.args[0].simplify()

    Eq << Eq[-1].this.find(Det).apply(discrete.det_block.to.zero)

    
    


if __name__ == '__main__':
    run()
# created on 2021-11-22
# updated on 2022-07-11
