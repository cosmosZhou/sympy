from util import *


@apply
def apply(le, is_continuous, is_differentiable):
    a, b = le.of(LessEqual)
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_differentiable, of_continuous
    fz, (z, _a, _b) = of_continuous(is_continuous)
    _fz, (_z, __a, __b) = of_differentiable(is_differentiable, open=False)
    assert _fz == fz
    assert _z == z
    assert _a == a == __a
    assert _b == b == __b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(a <= b, is_continuous(f, a, b), is_differentiable(f, a, b, open=False))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=b > a)

    Eq << Infer(b <= a, Equal(a, b), plausible=True)

    Eq << algebra.infer.given.ou.apply(Eq[-1]).reversed

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.all.imply.all.limits.restrict.apply(Eq[2], Interval(a, b, left_open=True, right_open=True))

    Eq << algebra.cond.imply.infer.apply(Eq[1] & Eq[-1], cond=b > a)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].reversed

    Eq << Eq[-1].this.rhs.apply(calculus.lt.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange)

    Eq << Eq[-1].this.rhs.apply(algebra.any.imply.any.limits.relax, domain=Interval(a, b))


if __name__ == '__main__':
    run()

# created on 2020-04-29
# updated on 2020-04-29
