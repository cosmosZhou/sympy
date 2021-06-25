from util import *


@apply
def apply(given):
    from axiom.algebra.square.to.mul.st.sum import dissect_variance

    dx, dy = given.of(LessEqual)

    ym, x, i, n = dissect_variance(dx)

    dy = dy.of(Expr ** 2)

    _ym, y_mean = dy.of(Expr - Expr)
    assert _ym == ym
    y_sum, m1 = y_mean.of(Expr / Expr)
    m = m1 - 1
    yj, (j, *ab) = y_sum.of(Sum)
    if ab:
        zero, _m = ab
        assert zero == 0
        assert _m == m1

    y = Lamda[j](yj).simplify()

    assert y[m] == ym

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2) + (ym - (Sum[i:n](x[i]) + ym) / (n + 1)) ** 2 + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2),
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m + 1]((y[j] - Sum[j:m + 1](y[j]) / (m + 1)) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo,))
    m = Symbol.m(domain=Range(2, oo))
    y = Symbol.y(real=True, shape=(m,))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    Eq << apply((y[m - 1] - Sum[i](x[i]) / n) ** 2 <= (y[m - 1] - Sum[j](y[j]) / m) ** 2)

    Eq << Eq[-1].rhs.args[0].this.apply(algebra.sum.to.mul.st.variance)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.rhs.find(Sum).split({n})

    

    Eq << Eq[-1].this.lhs.split({n})

    Eq << Eq[-1].find(Sum, Sum).this.split({n})

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(x[n], y[m - 1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.mul.st.variance)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.st.variance)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.to.mul.st.variance)

    Eq << algebra.le.imply.le.st.square.apply(Eq[0])

    Eq << Eq[-1].this.lhs.find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[1].find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[1].find(Sum).function.apply(algebra.square.negate)

    Eq << Eq[-1].this.rhs.args[0].find(Sum).limits_subs(i, j)


if __name__ == '__main__':
    run()

