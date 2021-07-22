from util import *


@apply
def apply(le, contains):
    from axiom.algebra.abs_sum.to.mul.sum import dissect_distance
    dx, dy = le.of(LessEqual)

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
    
    t, s = contains.of(Contains)
    assert s in Range(0, m)
    assert y[t] == yt

    return LessEqual(Sum[i:n]((x[i] - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2) + (yt - (Sum[i:n](x[i]) + yt) / (n + 1)) ** 2 + Sum[j:m]((y[j] - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2) - (yt - (Sum[j:m](y[j]) - yt) / (m - 1)) ** 2,
                     Sum[i:n]((x[i] - Sum[i:n](x[i]) / n) ** 2) + Sum[j:m]((y[j] - Sum[j:m](y[j]) / m) ** 2))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Function.x(real=True)
    m = Symbol.m(domain=Range(2, oo))
    y = Function.y(real=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    t = Symbol.t(integer=True, given=True)
    Eq << apply(abs(y(t) - Sum[i:n](x(i)) / n) <= abs(y(t) - Sum[j:m](y(j)) / m), Contains(t, Range(0, m)))

    t_ = Symbol.t(domain=Range(0, m))
    Eq << Eq[0]._subs(t, t_).this.apply(algebra.le_abs.imply.le.function, t_)

    Eq << Eq[-1].subs(t_, t)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()