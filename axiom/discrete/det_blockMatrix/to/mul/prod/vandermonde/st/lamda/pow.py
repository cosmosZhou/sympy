from util import *


@apply
def apply(self):
    ((r, _j), (j, _0, n1)), ((__j, i), j_limit, (_i, __0, n)) = self.of(Det[BlockMatrix[Lamda[Pow], Lamda[Pow]]])
    
    assert j_limit == (j, _0, n1)
    assert 0 == _0 == __0
    assert n1 == n + 1
    assert j == _j == __j
    assert i == _i
    
    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:n + 1](r ** j), Lamda[j:n + 1, i:n](j ** i)])))

    j, i = Eq[0].lhs.arg.args[1].variables
    E = Lamda[j:n + 1, i:n + 1]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].find(Lamda[Sum, Tuple, Tuple]).this().expr.simplify()

    _i = i.copy(domain=Range(n))
    _j = j.copy(domain=Range(n + 1))
    Eq << discrete.stirling2.to.mul_sum.apply(i, j)

    Eq << Eq[-1] * factorial(j)

    Eq << Eq[-1].reversed

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[3].subs(Eq[-1])

    Eq << Eq[-1].find(Lamda[Sum, Tuple]).this().expr.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << discrete.pow.to.sum.binomial.theorem.apply(r, -1, j, i)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], ShiftMatrix(n + 1, 0, n))

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.powsimp()

    

    

    

    

    

    

    

    

    

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2021-10-04
# updated on 2021-10-07