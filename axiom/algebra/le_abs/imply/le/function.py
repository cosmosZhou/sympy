from util import *


@apply
def apply(given, t):
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

    y = Lamda[j:m](yj).simplify()
    assert y[t] == yt
    assert t < m and t >= 0

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2) + (yt - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2 + Sum[j:m]((y[j] - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2) - (yt - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2,
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x, y = Function(real=True)
    m = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(0, m))
    Eq << apply(abs(y(t) - Sum[i:n](x(i)) / n) <= abs(y(t) - Sum[j:m](y(j)) / m), t)

    x_ = Symbol.x(Lamda[i:n](x(i)))
    Eq << x_[i].this.definition

    y_ = Symbol.y(Lamda[j:m](y(j)))
    Eq << y_[j].this.definition

    Eq << y_[t].this.definition

    Eq << Eq[0].subs(Eq[2].reversed, Eq[3].reversed, Eq[4].reversed)

    Eq << algebra.le_abs.imply.le.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[2], Eq[3], Eq[4])


if __name__ == '__main__':
    run()
