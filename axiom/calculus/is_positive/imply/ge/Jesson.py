from util import *


@apply
def apply(is_positive, w=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    if w is None:
        w = Symbol.w(domain=Interval(0, 1))

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
    Eq << Eq[1] - fx1

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)

    Eq << calculus.is_positive.imply.is_differentiable.within.apply(Eq[0], Min(x0, x1), Max(x0, x1))

    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq << calculus.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.closed.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function * w

    Eq.ge, Eq.lt = algebra.cond.imply.suffice.split.apply(Eq[-1], cond=x0 >= x1)

    Eq << Suffice(x0 >= x1, Equal(Min(x0, x1), x1), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.ge.imply.eq.min)

    Eq <<= Eq.ge & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Suffice(x0 >= x1, Equal(Max(x0, x1), x0), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.ge.imply.eq.max)

    Eq <<= Eq[-1] & Eq[-2]
    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()