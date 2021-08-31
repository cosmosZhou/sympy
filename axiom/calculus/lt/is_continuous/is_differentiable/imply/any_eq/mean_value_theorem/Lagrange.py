from util import *


@apply
def apply(lt, is_continuous, is_differentiable):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_differentiable, of_continuous
    a, b = lt.of(Less)
    if is_continuous.expr.is_Element:
        is_continuous, is_differentiable = is_differentiable, is_continuous

    fz, (z, _a, _b) = of_continuous(is_continuous)
    _fz, (_z, __a, __b) = of_differentiable(is_differentiable)

    assert _fz == fz
    assert _z == z
    assert _a == a == __a
    assert _b == b == __b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b, left_open=True, right_open=True)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    a, b = Symbol(real=True, given=True)
    f = Function(real=True)
    Eq << apply(a < b, is_continuous(f, a, b), is_differentiable(f, a, b))

    g = Function(eval=lambda x: (b - a) * f(x) - (f(b) - f(a)) * x)
    x = Symbol(real=True)
    Eq.g_definition = g(x).this.defun()

    Eq << Eq.g_definition.subs(x, a)

    Eq << Eq.g_definition.subs(x, b)

    Eq << Eq[-1] - Eq[-2]

    Eq.equal = Eq[-1].this.rhs.expand()

    Eq.is_continuous = Eq[1]._subs(f, g).copy(plausible=True)

    Eq << Eq.is_continuous.this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.rhs.defun()

    Eq << Eq[-1].this.expr.lhs.apply(calculus.limit.to.add)

    Eq << Eq[-1].this.expr.lhs.args[0].apply(calculus.limit.to.mul)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.mul)

    Eq <<= Eq[1] & Eq[-1]

    Eq <<= Eq[-1].this.expr.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << Eq[-1].this.expr.simplify()

    Eq << Eq[-1].this.expr.rhs.apply(algebra.mul.distribute)

    Eq.is_differentiable = Eq[2]._subs(f, g).copy(plausible=True)

    Eq << Eq.is_differentiable.this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.lhs.apply(calculus.derivative.to.add)

    Eq << Eq[-1].this.expr.apply(sets.el.given.el.add, f(b) - f(a))

    Eq << sets.all.imply.all_et.apply(Eq[2], simplify=None)

    Eq << Eq[-1].this.find(Unequal).apply(sets.interval_is_nonempty.imply.is_positive, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.is_positive.el.imply.el.mul)

    Eq << calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle.apply(Eq[0], Eq.is_continuous, Eq.is_differentiable, Eq.equal)

    Eq << Eq[-1].this.expr.lhs.expr.defun()

    Eq << Eq[-1].this.expr.lhs.apply(calculus.derivative.to.add)

    Eq << Eq[-1].this.expr - f(a)


if __name__ == '__main__':
    run()