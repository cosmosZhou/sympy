from util import *


@apply
def apply(is_nonnegative, self, offset):
    expr = is_nonnegative.of(Expr >= 0)
    _expr, (x, *ab) = self.of(Integral)
    assert _expr == expr
    if ab:
        a, b = ab
        limit = (x, a - offset, b - offset)
    else:
        limit = (x,)

    return Equal(self, Integral(expr._subs(x, x + offset), limit))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, y, a, b, c, d = Symbol(real=True)
    f, g = Function(real=True, integrable=True)
    Eq << apply(f(x) >= 0, Integral[x:a:b](f(x)), d)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=a > b)

    Eq <<= Eq[-2].this.find(Integral).apply(calculus.integral.to.piece), Eq[-1].this.find(Integral).apply(calculus.integral.to.piece)

    Eq <<= Eq[-2].this.find(Equal[~Integral]).apply(calculus.integral.to.piece), Eq[-1].this.find(Equal[~Integral]).apply(calculus.integral.to.piece)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq << -Eq[-2].this.rhs

    Eq << algebra.cond.imply.et.infer.split.apply(Eq[0], cond=a > b)

    Eq << Eq[-2].this.rhs.apply(calculus.ge_zero.imply.eq.integral.limits.offset.interval, Eq[-3].find(Integral), d)
    Eq << Eq[-1].this.rhs.apply(calculus.ge_zero.imply.eq.integral.limits.offset.interval, Eq[-4].find(Integral), d)


if __name__ == '__main__':
    run()
from . import interval
# created on 2020-05-25
