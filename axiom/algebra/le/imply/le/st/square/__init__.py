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

    y = Lamda[j](yj).simplify()

    return LessEqual((Sum[j:i, i:n]((x[i] - x[j]) ** 2) + Sum[i:n]((x[i] - yt) ** 2)) / (n + 1) + (Sum[j:i, i:m]((y[i] - y[j]) ** 2) - Sum[i:m]((y[i] - yt) ** 2)) / (m - 1),
                     (Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n + (Sum[j:i, i:m]((y[i] - y[j]) ** 2) / m)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    m = Symbol(domain=Range(2, oo))
    y = Symbol(real=True, shape=(m,))
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(m))
    Eq << apply(abs(y[t] - Sum[i](x[i]) / n) <= abs(y[t] - Sum[j](y[j]) / m))

    y_ = Symbol("y'", y @ SwapMatrix(m, t, m - 1))
    Eq << y_.this.definition

    Eq << y_[m - 1].this.definition

    Eq.y_last = Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq.le = Eq[0].subs(Eq.y_last.reversed)

    Eq << y_[t].this.definition

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << discrete.eq_matmul.imply.eq.sum.apply(Eq[2], j)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq.le.subs(Eq[-1])

    Eq << algebra.le.imply.le.st.square.pop_back.apply(Eq[-1])

    Eq << Eq[-1].rhs.args[0].args[1].this.apply(algebra.sum.to.add.split, cond={m - 1})

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_back)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.y_last)

    Eq << discrete.eq_matmul.imply.eq.sum.square.double_limits.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << discrete.eq_matmul.imply.eq.sum.square.offset.apply(Eq[2], y[t], j)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(algebra.square.negate)

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.find(-~Sum[Pow]).simplify()

    Eq << Eq[1].this.lhs.find(-~Sum[Pow]).limits_subs(i, j)

    Eq << Eq[-1].this.lhs.args[1].args[1].args[0].simplify()


if __name__ == '__main__':
    run()

from . import pop_back
# created on 2019-11-15
