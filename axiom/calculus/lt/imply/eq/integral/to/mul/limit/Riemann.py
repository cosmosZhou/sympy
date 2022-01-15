from util import *


@apply
def apply(lt, self, n=None, k=None):
    _a, _b = lt.of(Less)
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous(x)
    assert a == _a and b == _b
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a < b, Integral[x:a:b](f(x)))

    Eq << calculus.lt.imply.eq.integral.to.mul.limit.maxima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << calculus.lt.imply.eq.integral.to.mul.limit.minima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.eq.imply.eq.div.apply(Eq[-1], Eq[-2])

    Eq << calculus.lt.eq_limit.imply.eq.Darboux.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-27
