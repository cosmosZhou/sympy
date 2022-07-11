from util import *


@apply
def apply(self):
    (sgm, sgm_t), den = self.of((Expr - Expr) / Expr)
    (xi, xj), (j, _0, i), (i, __0, n) = sgm.of(Sum[(Expr - Expr) ** 2])
    (_xi, xt), (_i, _0, _n) = sgm_t.of(Sum[(Expr - Expr) ** 2])
    x, t = xt.of(Indexed)

    assert _xi == x[_i]
    if xi._has(j):
        xi, xi = xj, xi

    assert xi == x[i]
    assert xj == x[j]

    assert 0 == _0 == __0
    assert n == _n == den + 1
    assert t >= 0 and t < n

    return Equal(self, Sum[i:n]((x[i] - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2) - (xt - (Sum[i:n](x[i]) - xt) / (n - 1)) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    x = Symbol(integer=True, shape=(oo,))
    t = Symbol(domain=Range(n))
    Eq << apply((Sum[j:i, i:n]((x[i] - x[j]) ** 2) - Sum[i:n]((x[i] - x[t]) ** 2)) / (n - 1))

    y = Symbol(Lamda[i:n - 1](Piecewise((x[i], i < t),(x[i + 1], True))))
    Eq << y[i].this.definition

    Eq.y_sum = algebra.eq_piece.imply.eq.sum.apply(Eq[1], Sum[i:n-1](y[i]))

    Eq << algebra.sum_square.to.mul.st.variance.apply(Sum[i:n-1]((y[i] - Sum[i:n - 1](y[i]) / (n - 1)) ** 2))

    Eq << Eq[-1].subs(Eq.y_sum).reversed

    Eq << algebra.eq_piece.imply.eq.sum.apply(Eq[1], Eq[-1].rhs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.sum_square.to.add.st.double_limits.apply(Eq[-1].lhs.args[1])

    Eq << Eq[-1].subs(Eq.y_sum)

    Eq << algebra.eq_piece.imply.eq.sum.apply(Eq[1], Sum[i](y[i] ** 2))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[0].lhs.find(Sum).this.apply(algebra.sum_square.to.add.st.double_limits)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[0].lhs.find(-~Sum).this.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-3] + Eq[-1]

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=slice(0, 2))
    Eq << Eq[0].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2019-11-27
