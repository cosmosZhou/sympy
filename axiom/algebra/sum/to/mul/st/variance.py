from util import *


@apply
def apply(self):
    import axiom
    function, limit = self.of(Sum)
    x_sub_x_means = function.of(Basic ** 2)

    try:
        i, z, n = axiom.limit_is_Interval((limit,))
    except:
        (i,) = limit
        domain = function.domain_defined(i)
        z, n = domain.of(Range)

    assert z == 0
    xi, x_means = axiom.is_Subtract(x_sub_x_means)

    x, _i = xi.of(Indexed)
    assert _i == i

    x_sum = x_means * n

    xi, limit = x_sum.of(Sum)

    try:
        j, z, _n = axiom.limit_is_Interval((limit,))
    except:
        (j,) = limit
        domain = xi.domain_defined(j)
        z, _n = domain.of(Range)

    assert z == 0
    assert n == _n
    _x, _j = xi.of(Indexed)
    assert _j == j

    assert x == _x

    if j == i:
        j = self.generate_var(excludes={i}, integer=True, var='j')

    return Equal(self, Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n)


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True, shape=(oo,))

    Eq << apply(Sum[i:n]((x[i] - Sum[j:n](x[j]) / n) ** 2))

    Eq << Eq[-1].this.lhs.function.expand()

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Pow, Sum).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.lhs.find(Mul).args[2].apply(algebra.square.to.add.st.sum)

    Eq << Eq[-1].this.lhs.find(Mul).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Sum, Pow).apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1] * n

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.args[1].doit()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(j, i)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_front)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()

