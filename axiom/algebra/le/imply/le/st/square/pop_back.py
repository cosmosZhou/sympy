from util import *


@apply
def apply(given):
    from axiom.algebra.abs_sum.to.mul.sum import dissect_distance
    dx, dy = given.of(LessEqual)

    ym, x, i, n = dissect_distance(dx)

    _ym, y_mean = dy.of(Abs[Expr - Expr])

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

    return LessEqual((Sum[j:i, i:n]((x[i] - x[j]) ** 2) + Sum[i:n]((x[i] - ym) ** 2)) / (n + 1) + Sum[j:i, i:m]((y[i] - y[j]) ** 2) / m,
                     (Sum[j:i, i:n]((x[i] - x[j]) ** 2) / n + (Sum[j:i, i:m + 1]((y[i] - y[j]) ** 2) / (m + 1))))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, shape=(n,))
    m = Symbol(domain=Range(2, oo))
    y = Symbol(real=True, shape=(m,))
    i, j = Symbol(integer=True)
    Eq << apply(abs(y[m - 1] - Sum[i](x[i]) / n) <= abs(y[m - 1] - Sum[j](y[j]) / m))

    Eq << algebra.le.imply.le.square.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.square.to.mul.st.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.square.to.mul.st.sum)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.square.to.add.st.sum)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.square.to.add.st.sum)

    Eq.le_given = Eq[-1] * m ** 2

    Eq << Eq.le_given.rhs.this.find(2 * ~Sum).expr.apply(algebra.mul.to.add.square)

    Eq << Eq[-1].this.rhs.find(Mul).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.args[0]().expr.args[1].simplify()

    Eq.variance = Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_front)

    Eq << Eq.variance.rhs.args[1].this.apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.limits_subs(i, j)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1] + Eq.variance.rhs.args[0]

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.factor()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << Eq.variance.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Mul, Sum).expr.apply(algebra.square.negate)

    Eq << Eq[-1].this.rhs.find(Mul, Sum).apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1] + Eq.le_given.rhs.args[0]

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.mul.to.add)

    Eq << Eq.le_given.subs(Eq[-1])

    Eq.le_given = Eq[-1].this.rhs.args[1].apply(algebra.sum.to.mul)

    Eq << Eq.le_given.find(- ~Sum).this.apply(algebra.sum.to.add.split, cond={m - 1})

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_back)

    Eq << Eq[-1].this.rhs.args[0].limits_subs(i, j)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(algebra.square.negate)

    Eq << Eq.le_given.subs(Eq[-1])

    Eq << Eq[-1] - Eq[-1].rhs.args[-1]

    Eq << Eq[-1].this.rhs.collect(Eq[-1].rhs.find(Sum))

    Eq << Eq[-1] / (m - 1)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.args[0].find(Sum).apply(algebra.sum.limits.swap.subs)

    Eq.le_given = Eq[-1].this.lhs.args[0].find(Sum).expr.apply(algebra.square.negate)

    Eq << Eq[1] - Eq[1].rhs.args[1]

    Eq << Eq[-1].this.lhs.args[2].apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.collect(Eq[-1].lhs.args[-1].find(Sum))

    Eq << Eq[-1].this.lhs.args[2].args[0].ratsimp()

    Eq << Eq[-1] * m

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={m - 1})

    Eq << Eq[-1] - Eq[-1].rhs.args[-1]

    Eq << Eq[-1].this.lhs.collect(Eq[-2].rhs.args[-1])

    Eq << Eq[-1].this.lhs.args[0].args[0].ratsimp()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.push_back)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.domain_defined.delete)

    assert Eq[-1].rhs == Eq.le_given.rhs
    Eq.le_plausible = LessEqual(Eq[-1].lhs, Eq.le_given.lhs, plausible=True)

    Eq << Eq.le_plausible.this.apply(algebra.le.simplify.terms.common)

    Eq << Eq[-1] / m

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.find(Sum).expr.apply(algebra.square.negate)

    Eq << Eq[-1] - Eq[-1].lhs.args[0]

    Eq << Eq[-1].this.rhs.collect(Eq[-2].lhs.find(Sum))

    Eq.is_nonnegative = algebra.le.given.ge_zero.apply(Eq[-1])

    x_ = Symbol('x', Lamda[i](y[m - 1] - x[i]))
    Eq <<= x_[i].this.definition, x_[j].this.definition

    Eq <<= Eq[-2] + x[i] - x_[i], Eq[-1] + x[j] - x_[j]

    Eq.is_nonnegative = Eq.is_nonnegative.subs(Eq[-2], Eq[-1])

    Eq << Eq.is_nonnegative.lhs.args[0].find(Sum).this.expr.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.args[0]().expr.args[1].simplify()

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.args[1].doit()

    Eq << Eq[-1].this.rhs.args[0].limits_subs(i, j)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.to.add.push_front)

    Eq << Add(*Eq[-1].rhs.args[:2]).this.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.factor()

    Eq << Eq[-1].this.rhs.limits_subs(j, i)

    #Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)
    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.to.mul)

    Eq << Eq.is_nonnegative.subs(Eq[-1])

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.collect(Eq[-1].lhs.find(Sum))

    Eq << Eq[-1].this.lhs.collect(Eq[-1].lhs.find(Sum))

    Eq << Eq[-1].this.lhs.args[1].args[0].ratsimp()

    Eq << Eq[-1].this.lhs.args[0].args[0].ratsimp()

    Eq << Eq[-1] * (n ** 2 * (m - 1) * (n + 1) / (m + n))

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.ratsimp()

    Eq << (Sum[i](x_[i]) ** 2).this.apply(algebra.square.to.add.st.sum)

    Eq << Eq[-1].this.rhs.args[0].simplify()

    Eq << GreaterEqual(Sum[i](x_[i]) ** 2, 0, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << algebra.le.le.imply.le.transit.apply(Eq.le_plausible, Eq.le_given)


if __name__ == '__main__':
    run()

# created on 2019-11-09
