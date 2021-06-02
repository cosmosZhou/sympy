from util import *


@apply
def apply(*given):
    from axiom.discrete.combinatorics.catalan.is_positive import is_catalan_series
    Cn, n = is_catalan_series(*given)
    return Equal(Cn, binomial(n * 2, n) / (n + 1))


@prove
def prove(Eq):
    from axiom import calculus, discrete, sets, algebra
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)

    C = Symbol.C(shape=(oo,), integer=True)

    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    x = Symbol.x(domain=Interval(0, S.One / 4, left_open=True))

    def g(x):
        return Sum[n:oo](C[n] * x ** n)

    g = Function.g(eval=g)

    Eq.g_definition = g(x).this.defun()

    Eq << Eq[1] * x ** n

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (n, 0, oo))

    Eq << calculus.series.infinite.product.apply(C, C, n=n, k=k, x=x)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition ** 2

    Eq.g_squared = algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition.this.rhs.split(Slice[1:])

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.rhs.limits_subs(n, n + 1)

    Eq << Eq.g_squared * x

    Eq << Eq[-1].this.lhs.astype(Sum)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-3])

    Eq.ou = Eq[-1].apply(algebra.eq.imply.ou.quadratic, x=g(x), simplify=False)

    Eq.negative_sqrt = Eq.ou.args[0].copy(plausible=True)

    Eq.positive_sqrt = Exists[x:x < S.One / 4](Eq.ou.args[1], plausible=True)

    x_quote = Symbol("x'", domain=Interval(0, S.One / 4, left_open=True, right_open=True))

    Eq.positive_sqrt_quote = Eq.positive_sqrt.limits_subs(x, x_quote)

    Eq << Derivative[x_quote](Eq.positive_sqrt_quote.rhs).this.doit()

    Eq << Less(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].this.lhs.subs(Eq[-2].reversed)

    Eq << calculus.is_negative.imply.gt.monotony.apply(Eq[-1])

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq.positive_sqrt_quote, Eq[-1], reverse=True)

    Eq.any_gt = algebra.any.imply.any.relax.apply(Eq[-1], x_quote, x)

    Eq << calculus.eq.imply.eq.derive.apply(Eq.g_definition, (x,), simplify=None)

    Eq << Eq[-1].this.rhs.apply(calculus.derivative.to.sum)

    Eq << Eq[-1].this.rhs.split({0})

    Eq.g_derivative = Eq[-1].this.rhs.astype(Sum)

    Eq << discrete.combinatorics.catalan.is_positive.apply(Eq[0], Eq[1])

    Eq << Eq[-1] * x ** (n - 1)

    Eq << algebra.gt.imply.gt.sum.multiply.apply(Eq[-1], (n, 0, oo))

    Eq << Eq[-1].this.lhs.subs(Eq.g_derivative.reversed)

    Eq << calculus.is_positive.imply.le.monotony.apply(Eq[-1])

    Eq << Eq.ou.subs(x, S.One / 4)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.any_gt)

    Eq << ~Eq.positive_sqrt

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(algebra.ge.imply.eq.squeeze.interval)

    Eq.all_ne = algebra.ou.imply.all.apply(Eq[-1], pivot=-1, wrt=x)

    Eq << Eq.ou.apply(algebra.cond.imply.et.all, cond=x < S.One / 4)

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=1)

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, x)

    Eq << Eq[-1].this.find(NotContains).simplify()

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=-1, wrt=x)

    Eq <<= Eq.all_ne & Eq[-1]

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].forall((x,))

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << Eq.negative_sqrt.apply(algebra.cond.given.et.all, cond=x < S.One / 4)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.given.ou.interval)

    Eq << calculus.series.infinite.binomial.apply(S.One / 2, x=-4 * x, n=n)

    Eq << discrete.combinatorics.binomial.half.apply(n)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].function.powsimp()

    Eq << Eq[-1].this.rhs.args[1].split(Slice[1:])

    Eq << 1 - Eq[-1]

    Eq << Eq[-1].this.rhs.limits_subs(n, n + 1)

    Eq << Eq[-1] / (x * 2)

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1] + Eq.negative_sqrt

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.distribute)

    Eq.g_series = Eq[-1].this.find(Mul).apply(algebra.mul.cancel, 2)

    Eq << discrete.combinatorics.binomial.fraction.apply(2 * n + 2, n + 1)

    Eq << discrete.combinatorics.binomial.expand.apply(2 * n + 1, n + 1)

    Eq << Eq[-2].subs(Eq[-1]) * (2 * n + 2)

    Eq << Eq.g_series.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.astype(Sum)

    Eq << Eq[-1].this.rhs.function.ratsimp()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq.g_definition)

    Eq << calculus.eq.imply.eq.series.infinite.coefficient.apply(Eq[-1].reversed, x=x)


if __name__ == '__main__':
    run()

