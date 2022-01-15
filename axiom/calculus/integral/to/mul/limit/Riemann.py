from util import *


@apply
def apply(self, n=None, k=None):
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=a < b)

    Eq << (a < b).this.apply(calculus.lt.imply.eq.integral.to.mul.limit.maxima.Darboux, Eq[0].lhs)

    Eq << (a < b).this.apply(calculus.lt.imply.eq.integral.to.mul.limit.minima.Darboux, Eq[0].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lt.imply.gt_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.eq.imply.eq.div)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.lt.eq_limit.imply.eq.Darboux)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[2], cond=a > b)

    Eq <<= Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq << Eq[-2].this.lhs.apply(calculus.gt.imply.eq.integral.to.limit.Riemann, Eq[0].lhs)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-08
