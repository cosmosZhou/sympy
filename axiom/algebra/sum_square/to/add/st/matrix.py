from util import *


@apply
def apply(self):
    (xij, mean), (j, _0, n), (i, __0, m) = self.of(Sum[Pow[Expr - Expr, 2]])
    assert 0 == _0 == __0
    sgm = mean * (m * n)
    _xij, *limits = sgm.of(Sum)
    assert limits == [(j, 0, n), (i, 0, m)]
    assert xij == _xij
    return Equal(self, n * Sum[i:m]((Sum[j:n](xij) / n - mean) ** 2) + Sum[j:n, i:m]((xij - Sum[j:n](xij) / n) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    m, n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True, shape=(oo, oo))
    Eq << apply(Sum[j:n, i:m]((x[i, j] - Sum[j:n, i:m](x[i, j]) / (m * n)) ** 2))

    x_bar = Symbol(r"\overline{x}", Sum[j:n, i:m](x[i, j]) / (m * n))
    _x_bar = Symbol(r"\overline{x'}", Lamda[i:m](Sum[j:n](x[i, j])) / n)
    Eq <<= x_bar.this.definition, _x_bar[i].this.definition

    Eq <<= Eq[-2] * (m * n), Eq[-1] * n, algebra.eq.imply.eq.sum.apply(Eq[-1], (i, 0, m))

    Eq.eq_sum = Eq[-3].reversed

    Eq.eq_sum_j = Eq[-2].reversed

    Eq.eq_sum_quote = Eq[-1].subs(Eq.eq_sum)

    Eq << Eq[0].subs(Eq[1].reversed, Eq[2].reversed)

    Eq << Sum[j:n, i:m]((x[i, j] - x_bar) ** 2).this.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.to.mul)

    Eq.St = Eq[-1].subs(Eq.eq_sum)

    Eq << Sum[i:m]((_x_bar[i] - x_bar) ** 2).this.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].subs(Eq.eq_sum_quote)

    Eq << Eq[-1] * n

    Eq.SA = Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Sum[j:n, i:m]((x[i, j] - _x_bar[i]) ** 2).this.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.limits.separate)

    Eq << Eq[-1].subs(Eq.eq_sum_j)

    Eq << Eq[-1].this.find(Sum[Mul]).apply(algebra.sum.to.mul)

    Eq << Eq[-1] + Eq.SA

    Eq << Eq.St.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()