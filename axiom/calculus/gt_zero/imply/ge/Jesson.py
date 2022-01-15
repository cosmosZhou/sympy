from util import *


@apply
def apply(is_positive, w=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    if w is None:
        w = Symbol.w(domain=Interval(0, 1))
    else:
        assert Element(w, Interval(0, 1))

    domain = x_.domain
    assert domain.left_open and domain.right_open
    x0, x1 = Symbol(domain=domain)
    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    a, b = Symbol(real=True)
    x = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol(domain=Interval(0, 1))
    f = Function(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0)

    (w, fx0), (_w, fx1) = Eq[1].lhs.of(Mul + Mul)
    x0 = fx0.arg
    x1 = fx1.arg
    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=x0 <= x1)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=x0 <= x1)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.le.gt_zero.imply.ge.Jesson, w=w)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=x0 > x1)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.gt.imply.le.relax)

    Eq << Eq[-1].this.rhs.apply(calculus.le.gt_zero.imply.ge.Jesson, w=1-w)


if __name__ == '__main__':
    run()
# created on 2020-05-12
