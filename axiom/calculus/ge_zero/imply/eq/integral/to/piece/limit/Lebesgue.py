from util import *


@apply
def apply(is_nonnegative, self, n=None, k=None):
    fx = is_nonnegative.of(Expr >= 0)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    fx, (x, a, b) = self.of(Integral)
    assert fx.is_integrable(x, a, b)

    return Equal(self, Piecewise((-Sup[x:b:a](fx) * Limit[n:oo](Sum[k:n](Measure({Element(x, Interval(b, a)) : fx >= Sup[x:b:a](fx) / n * k})) / n), a > b), (Sup[x:a:b](fx) * Limit[n:oo](Sum[k:n](Measure({Element(x, Interval(a, b)) : fx >= Sup[x:a:b](fx) / n * k})) / n), True)))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, finite=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:a:b](f(x)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=a > b)

    Eq <<= Eq[-2].this.find(Integral).apply(calculus.integral.to.piece), Eq[-1].this.find(Integral).apply(calculus.integral.to.piece)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << -Eq[-2].this.rhs

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=a > b)

    Eq <<= Eq[-2].this.rhs.apply(calculus.ge_zero.imply.eq.integral.to.mul.limit.Lebesgue, Eq[-3].find(Integral)), Eq[-1].this.rhs.apply(calculus.ge_zero.imply.eq.integral.to.mul.limit.Lebesgue, Eq[-4].find(Integral))


if __name__ == '__main__':
    run()
# created on 2020-05-25
