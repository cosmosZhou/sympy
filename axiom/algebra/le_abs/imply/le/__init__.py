from util import *


@apply
def apply(given):
    from axiom.algebra.abs_sum.to.mul.sum import dissect_distance
    dx, dy = given.of(LessEqual)

    yt, x, i, n = dissect_distance(dx)

    _yt, y_mean = dy.of(Abs[Expr - Expr])

    assert _yt == yt
    y_sum, m = y_mean.of(Expr / Expr)

    yj, (j, *ab) = y_sum.of(Sum)
    if ab:
        zero, _m = ab
        assert zero == 0
        assert _m == m

    y, _j = yj.of(Indexed)
    assert j == _j
    _y, t = yt.of(Indexed)
    assert y == _y
    assert t < m

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2) + (yt - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2 + Sum[j:m]((y[j] - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2) - (yt - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2,
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(oo,))
    m = Symbol(domain=Range(2, oo))
    y = Symbol(real=True, shape=(m,))
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(m))
    Eq << apply(abs(y[t] - Sum[i](x[i]) / n) <= abs(y[t] - Sum[j](y[j]) / m))

    Eq << Eq[-1].rhs.args[0].this.apply(algebra.sum_square.to.mul.st.variance)

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.split, cond={n})

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-1].find(Sum, Sum).this.apply(algebra.sum.to.add.pop_back)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(x[n], y[t])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum_square.to.mul.st.variance)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum_square.to.mul.st.variance)

    Eq << Eq[-1].this.rhs.args[0].find(Sum).limits_subs(i, j)

    Eq << algebra.le.imply.le.st.square.apply(Eq[0])

    Eq << Eq[-1].this.lhs.args[1].find(Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.mul.to.add.st.variance)

    Eq << Eq[-1].this.lhs.find(Add, Mul, Add, Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.find(Sum, Add, Mul, Add, Sum).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[2].limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[0].find(Expr ** 2).apply(algebra.square.negate)


if __name__ == '__main__':
    run()


from . import function
# created on 2019-11-28
