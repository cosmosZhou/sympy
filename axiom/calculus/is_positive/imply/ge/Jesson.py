from util import *


@apply
def apply(is_positive, w=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    if w is None:
        w = Symbol.w(domain=Interval(0, 1))
    else:
        assert Contains(w, Interval(0, 1))

    domain = x_.domain
    assert domain.left_open and domain.right_open
    x0 = Symbol.x0(domain=domain)
    x1 = Symbol.x1(domain=domain)
    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(domain=Interval(a, b, left_open=True, right_open=True))
    w = Symbol.w(domain=Interval(0, 1))
    f = Function.f(real=True)
    Eq << apply(Derivative(f(x), (x, 2)) > 0)

    (w, fx0), (_w, fx1) = Eq[1].lhs.of(Mul + Mul)
    x0 = fx0.arg
    x1 = fx1.arg
    Eq << algebra.cond.given.suffice.split.apply(Eq[-1], cond=x0 <= x1)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=x0 <= x1)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.le.is_positive.imply.ge.Jesson, w=w)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=x0 > x1)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.gt.imply.le.relax)

    Eq << Eq[-1].this.rhs.apply(calculus.le.is_positive.imply.ge.Jesson, w=1-w)


if __name__ == '__main__':
    run()