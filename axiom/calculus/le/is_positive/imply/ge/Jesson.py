from util import *


@apply
def apply(le, is_positive, w=None):
    x0, x1 = le.of(LessEqual)
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2

    if w is None:
        w = Symbol.w(domain=Interval(0, 1))
    else:
        assert w >= 0 and w <= 1
    domain = x_.domain
    assert domain.left_open and domain.right_open

    return GreaterEqual(w * fx._subs(x_, x0) + (1 - w) * fx._subs(x_, x1), fx._subs(x_, w * x0 + (1 - w) * x1))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    x = Symbol.x(domain=domain)
    f = Function.f(real=True)
    x0 = Symbol.x0(domain=domain, given=True)
    x1 = Symbol.x1(domain=domain, given=True)
    w = Symbol.w(domain=Interval(0, 1), given=True)
    Eq << apply(x0 <= x1, Derivative(f(x), (x, 2)) > 0, w=w)

    (w, fx0), (_w, fx1) = Eq[-1].lhs.of(Mul + Mul)
    x0 = fx0.arg
    x1 = fx1.arg
    Eq << calculus.is_positive.imply.is_differentiable.within.apply(Eq[1], x0, x1)

    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq << calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.closed.apply(Eq[0], Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function * w

    Eq.is_nonpositive = Eq[0] - x1

    Eq <<= algebra.le.imply.le.mul.apply(Eq.is_nonpositive, w) + x1, algebra.ge.imply.ge.mul.apply(Eq[0].reversed, 1 - w) + w * x0

    Eq << Eq[-2].this.find(Mul).apply(algebra.mul.to.add, simplify=None)

    Eq.ge = Eq[-2].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add, simplify=None)

    Eq.le = Eq[-1].this.lhs.apply(algebra.add.collect, factor=x1)

    Eq.all_is_positive = algebra.cond.imply.all.apply(Eq[1], x)

    Eq.x0_contains, Eq.x1_contains = Contains(x0, domain, plausible=True), Contains(x1, domain, plausible=True)

    Eq.x_mean_contains = sets.contains.contains.imply.contains.interval.apply(Eq.x0_contains, Eq.x1_contains, w)

    Eq <<= calculus.contains.contains.all_is_positive.imply.is_differentiable.apply(Eq.x0_contains, Eq.x_mean_contains, Eq.all_is_positive), calculus.contains.contains.all_is_positive.imply.is_differentiable.apply(Eq.x_mean_contains, Eq.x1_contains, Eq.all_is_positive)

    x_ = Symbol("x'", real=True)
    Eq << Eq[-2].limits_subs(Eq[-2].variable, x_)

    x__ = Symbol("x''", real=True)
    Eq << Eq[-1].limits_subs(Eq[-1].variable, x__)

    Eq <<= calculus.is_differentiable.imply.is_continuous.apply(Eq[-2]), calculus.is_differentiable.imply.is_continuous.apply(Eq[-1])

    Eq <<= calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.closed.apply(Eq.ge.reversed, Eq[-2], Eq[-4]), calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.closed.apply(Eq.le, Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.function.rhs.args[0].apply(algebra.add.collect), Eq[-1].this.function.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq <<= Eq[-2].this.function.rhs.args[0].apply(algebra.add.collect, factor=1 - w), Eq[-1].this.function.rhs.find(Add[Mul]).apply(algebra.add.to.mul)

    Eq <<= Eq[-2].this.function * w, Eq[-1].this.function * (1 - w)

    Eq << algebra.any.any.imply.any_et.apply(Eq[-2], Eq[-1], simplify=None)

    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.sub)

    Eq << Eq[-1].this.function.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.function.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.function.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.function.lhs.apply(algebra.add.collect, factor=f(x1))

    Eq.any = Eq[-1].this.function.rhs.apply(algebra.add.collect, factor=w * (1 - w) * (x1 - x0))

    Eq.suffice = Eq.any.limits_cond.this.apply(sets.contains.contains.imply.le)

    Eq <<= sets.contains.contains.imply.subset.interval.apply(Eq.x0_contains, Eq.x_mean_contains), sets.contains.contains.imply.subset.interval.apply(Eq.x_mean_contains, Eq.x1_contains)

    Eq <<= algebra.cond.imply.suffice.apply(Eq[-2], cond=Eq.suffice.lhs.args[0]), algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq.suffice.lhs.args[1])

    Eq <<= algebra.suffice.imply.suffice.et.apply(Eq[-2]), algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.subset.imply.contains), Eq[-1].this.rhs.apply(sets.contains.subset.imply.contains)

    Eq << algebra.suffice.suffice.imply.suffice.et.apply(Eq[-2], Eq[-1])

    Eq << algebra.cond.imply.suffice.apply(Eq.all_is_positive, cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2] & Eq.suffice

    Eq << Eq[-1].this.rhs.apply(calculus.all_is_positive.contains.contains.le.imply.le)

    Eq.is_nonnegative = Eq[-1].this.rhs.apply(algebra.le.imply.is_nonnegative)

    Eq << GreaterEqual(w * (1 - w), 0, plausible=True)

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(Eq[-1], -Eq.is_nonpositive)

    Eq << algebra.cond.imply.suffice.apply(Eq[-1], cond=Eq[-3].lhs)

    Eq <<= Eq[-1] & Eq.is_nonnegative

    Eq <<= Eq[-1].this.rhs.apply(algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative)

    Eq << algebra.suffice.imply.all.apply(Eq[-1], wrt=(x_, x__))

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.function.apply(algebra.ge.eq.imply.ge.transit)

    Eq << Eq[-1] + Eq[2].rhs


if __name__ == '__main__':
    run()