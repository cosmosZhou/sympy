from util import *


@apply
def apply(self):
    y, x, i, n = dissect_variance(self)
    return Equal(self, Sum[i:n](y - x[i]) ** 2 / n ** 2)


def dissect_distance(variance):
    ym, x_mean = variance.of(Abs[Expr - Expr])
    x_sum, n = x_mean.of(Expr / Expr)
    xi, (i, *ab) = x_sum.of(Sum)
    x = Lamda[i](xi).simplify()
    if ab:
        zero, _n = ab
        assert zero == 0
        assert _n == n

    return ym, x, i, n

def dissect_variance(variance):
    dx = variance.of(Expr ** 2)
    ym, x_mean = dx.of(Expr - Expr)

    x_sum, n = x_mean.of(Expr / Expr)
    xi, (i, *ab) = x_sum.of(Sum)
    x = Lamda[i](xi).simplify()
    if ab:
        zero, _n = ab
        assert zero == 0
        assert _n == n

    return ym, x, i, n


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    m = Symbol.m(integer=True, positive=True)
    y = Symbol.y(real=True)
    i = Symbol.i(integer=True)
    Eq << apply((y - Sum[i](x[i]) / n) ** 2)

    x_ = Symbol.x(Lamda[i](y - x[i]))
    Eq << x_[i].this.definition

    Eq << Eq[-1] - y

    Eq << -Eq[-1]

    Eq << Eq[0].lhs.this.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)

    #Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul)
    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].subs(x_[i].this.definition)

    Eq << Eq[0].this.rhs.find(Sum).apply(algebra.sum.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

