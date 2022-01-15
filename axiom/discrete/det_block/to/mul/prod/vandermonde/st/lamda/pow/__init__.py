from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Lamda[Pow], Lamda[Pow]]])

    S[j], S[0], S[n + 1:n > 0] = j_limit

    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:n + 1](r ** j), Lamda[j:n + 1, i:n](j ** i)])))

    j, i = Eq[0].lhs.arg.args[1].variables
    E = Lamda[j:n + 1, i:n + 1]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].find(Lamda[Sum, Tuple[2]]).this().expr.simplify()

    _i = i.copy(domain=Range(n))
    _j = j.copy(domain=Range(n + 1))
    Eq << discrete.stirling2.to.mul_sum.apply(i, j)

    Eq << Eq[-1] * factorial(j)

    Eq << Eq[-1].reversed

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[-1].find(Lamda[Sum, Tuple]).this().expr.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << ShiftMatrix(n + 1, 0, n) @ Eq[-1]

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.powsimp()


if __name__ == '__main__':
    run()
# created on 2021-10-04
# updated on 2021-11-25
from . import n2
from . import mn
