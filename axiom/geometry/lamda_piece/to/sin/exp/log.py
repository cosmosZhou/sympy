from util import *


@apply
def apply(self):
    (((i, (b, (j, d))), (S[j], S[0])), (S[i / b ** ((j - 1) / d)], S[S.true])), (S[j], S[0], S[d]), (S[i], S[0], n) = self.of(Lamda[Piecewise[ExprCondPair[sin[Expr * Expr ** (-Expr / Expr)], Equal[Expr % 2]], ExprCondPair[cos]]])
    j = Lamda[j:d](j)
    return Equal(self, sin(S.Pi / 2 * (j % 2) + (Lamda[i:n](i) * OneMatrix(d, n)).T * exp(-2 * (j // 2) / d * log(b))))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    n, b = Symbol(positive=True, integer=True)
    d = Symbol(integer=True, positive=True, even=True)
    i, j = Symbol(integer=True)
    Eq << apply(Lamda[j:d, i:n](Piecewise((sin(i / b ** (j / d)), Equal(j % 2, 0)), (cos(i / b ** ((j - 1) / d)), True))))

    Eq << Eq[0].this.lhs.expr.apply(geometry.piece.to.sin.sinusoidal)

    i = Symbol(domain=Range(n))
    j = Symbol(domain=Range(d))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], (i, j))

    
    Eq << geometry.eq_sin.given.eq.apply(Eq[-1])
    Eq << Eq[-1].this.find(Mul[Log]).apply(algebra.mul.to.log)
    


if __name__ == '__main__':
    run()
# created on 2022-01-23
