from util import *


@apply
def apply(eq_C):
    (C, S[C]), C_quote = eq_C.of(Equal[Mul[Transpose[OneMatrix * ReducedSum[Expr ** 2] ** (1 / 2)] ** -1]])
    return abs(C_quote @ C_quote.T) <= 1


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n, d = Symbol(domain=Range(2, oo))
    C, C_quote = Symbol(shape=(n, d), real=True)
    Eq << apply(Equal(C_quote, C / (sqrt(ReducedSum(C * C) * OneMatrix(d, n))).T))

    Eq << algebra.abs_le.given.et.apply(Eq[1])

    Eq <<= algebra.le.given.all.le.apply(Eq[-2]), algebra.ge.given.all.ge.apply(Eq[-1])

    i = Eq[-1].find(Indexed).index
    Eq <<= algebra.le.given.all.le.apply(Eq[-2]), algebra.ge.given.all.ge.apply(Eq[-1])

    j = Eq[-1].find(Indexed[2]).index
    Eq <<= Eq[-2].subs(Eq[0]), Eq[-1].subs(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(discrete.matmul.to.reducedSum), Eq[-1].this.lhs.apply(discrete.matmul.to.reducedSum)

    Eq << Eq[0][i]

    Eq << algebra.eq.imply.ne_zero.domain_definition.apply(Eq[-1])

    Eq << algebra.ne_zero.imply.gt_zero.apply(Eq[-1])

    Eq << Eq[-1].subs(i, j)

    Eq <<= algebra.gt_zero.gt_zero.imply.le.one.apply(Eq[-1], Eq[-2]), algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1]) * algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-2])

    Eq << algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[-2])

    Eq << algebra.abs_le.imply.et.apply(Eq[-1])

    Eq << algebra.gt_zero.le.imply.le.div.apply(Eq[-4], Eq[-2])

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq[-4], Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-04-02
