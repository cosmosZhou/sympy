from util import *


@apply
def apply(gt, self, n=None, k=None):
    _a, _b = gt.of(Greater)
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')

    assert a == _a and b == _b
    assert fx.is_continuous(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a > b, Integral[x:a:b](f(x)))

    Eq << algebra.gt.imply.lt.reverse.apply(Eq[0])

    Eq << calculus.lt.imply.eq.integral.to.mul.limit.Riemann.apply(Eq[-1], Integral[x:b:a](f(x)))

    Eq << -Eq[-1]

    Eq.eq_integral = Eq[-1].this.lhs.apply(calculus.neg.to.integral)

    [(k, _0, n)] = Eq.eq_integral.find(Sum).limits
    Eq << Eq.eq_integral.find(Sum).this.apply(algebra.sum.limits.subs.negate, k, n - k)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.collect, k / n)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.piece.push_front)

    Eq << Eq[-1].this.find(GreaterEqual).simplify()

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.piece.pop_back)

    Eq << Eq[-1].this.find(LessEqual).reversed

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.piece)

    Eq << Eq.eq_integral.subs(Eq[-1])

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.piece.subs)

    Eq << Eq[-1].this.find(Limit[~Mul]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.add)

    Eq << Eq[-1].this.find(Limit).doit()
    Eq << Eq[-1].this.find(Limit).doit()


if __name__ == '__main__':
    run()
# created on 2020-05-28
