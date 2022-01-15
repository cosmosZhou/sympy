from util import *


@apply
def apply(self):
    (xi, xj), (j, _0, i), (i, __0, n) = self.of(Sum[Pow[Expr - Expr, 2]])
    assert 0 == _0 == __0
    if not xi._has(i):
        xi, xj = xj, xi
    assert xj._subs(j, i) == xi
    return Equal(self, n * Sum[i:n](xi ** 2) - Sum[i:n](xi) ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(real=True, shape=(oo,))
    Eq << apply(Sum[j:i, i:n]((x[i] - x[j]) ** 2))

    Eq << Eq[0].this.lhs.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.args[2].apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.lhs.args[1].limits_subs(j, i)

    Eq << Eq[-1].this.lhs.args[1].expr.apply(algebra.mul.to.add)

    Eq << -Eq[-1].this.lhs.args[1].apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(2 * ~Sum).apply(algebra.sum_mul.to.add.st.double_limits)


if __name__ == '__main__':
    run()
# created on 2019-11-12
