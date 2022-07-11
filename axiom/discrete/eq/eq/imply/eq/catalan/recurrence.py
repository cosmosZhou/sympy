from util import *


@apply
def apply(eq, eq1):
    from axiom.discrete.eq.eq.imply.gt_zero.catalan import is_catalan_series
    Cn, n = is_catalan_series(eq, eq1)
    return Equal(Cn, binomial(n * 2, n) / (n + 1))


@prove
def prove(Eq):
    from axiom import algebra, calculus, discrete, sets

    n, k = Symbol(integer=True)
    C = Symbol(shape=(oo,), integer=True)
    Eq << apply(Equal(C[0], 1),
                Equal(C[n + 1], Sum[k:n + 1](C[k] * C[n - k])))

    
    g = Function(extended_real=True)
    x = Symbol(real=True)
    g[x] = Sum[n:oo](C[n] * x ** n)
    
    x = Symbol(domain=Interval(0, S.One / 4, left_open=True))
    Eq.g_definition = g(x).this.defun()

    Eq << Eq[1] * x ** n

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (n, 0, oo))

    Eq << calculus.mul_sum.to.sum_sum.apply(C, C, n=n, k=k, x=x)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition ** 2

    Eq.g_squared = algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << Eq.g_definition.this.rhs.apply(algebra.sum.to.add.pop_front)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1] - 1

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq.g_squared * x

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.sum)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-3])

    Eq << algebra.eq.imply.is_zero.apply(Eq[-1])

    Eq.ou = Eq[-1].apply(algebra.poly_is_zero.imply.et.infer.quadratic, x=g(x), simplify=False)

    Eq.negative_sqrt = Eq.ou.args[0].copy(plausible=True)

    Eq.positive_sqrt = Any[x:x < S.One / 4](Eq.ou.args[1], plausible=True)

    x_quote = Symbol(domain=Interval(0, S.One / 4, left_open=True, right_open=True))
    Eq.positive_sqrt_quote = Eq.positive_sqrt.limits_subs(x, x_quote)

    Eq << Derivative[x_quote](Eq.positive_sqrt_quote.rhs).this.doit()

    Eq << Less(Eq[-1].rhs, 0, plausible=True)

    Eq << Eq[-1].this.lhs.subs(Eq[-2].reversed)

    Eq << calculus.lt_zero.imply.gt.monotony.apply(Eq[-1])

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq.positive_sqrt_quote, Eq[-1], reverse=True)

    Eq.any_gt = algebra.any.imply.any.limits.relax.subs.apply(Eq[-1], x_quote, x)

    Eq << calculus.eq.imply.eq.derive.apply(Eq.g_definition, (x,), simplify=None)

    Eq << Eq[-1].this.rhs.apply(calculus.derivative.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={0})

    Eq.g_derivative = Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << discrete.eq.eq.imply.gt_zero.catalan.apply(Eq[0], Eq[1])

    Eq << Eq[-1] * x ** (n - 1)

    Eq << algebra.gt.imply.gt.sum.mul.apply(Eq[-1], (n, 0, oo))

    Eq << Eq[-1].this.lhs.subs(Eq.g_derivative.reversed)

    Eq << calculus.gt_zero.imply.le.monotony.apply(Eq[-1])

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

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=-1, wrt=x)

    Eq <<= Eq.all_ne & Eq[-1]

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << algebra.cond.imply.all.apply(Eq[-1], x)

    Eq << algebra.all.imply.ou.apply(Eq[-1])

    Eq << Eq.negative_sqrt.apply(algebra.cond.given.et.all, cond=x < S.One / 4)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(sets.notin.given.ou.interval)

    Eq << calculus.pow.to.sum.binom.apply((1 - 4 * x) ** (S.One / 2), n=n)

    Eq << discrete.binom.to.mul.half.apply(n)

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.args[1].expr.powsimp()

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.to.add.pop_front)

    Eq << 1 - Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[-1] / (x * 2)

    Eq << Eq[-1] + Eq.negative_sqrt

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.distribute)

    Eq.g_series = Eq[-1].this.find(Mul).apply(algebra.mul.cancel, 2)

    Eq << discrete.mul.binom.fraction.apply(2 * n + 2, n + 1)

    Eq << Eq[-1].this.rhs.args[-1].apply(discrete.binom.to.mul.binom) * (2 * n + 2)

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq.g_series)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.expr.ratsimp()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq.g_definition)

    Eq << calculus.eq.imply.eq.series.infinite.coefficient.apply(Eq[-1].reversed, x=x)





if __name__ == '__main__':
    run()

# created on 2020-10-21
# updated on 2021-11-25