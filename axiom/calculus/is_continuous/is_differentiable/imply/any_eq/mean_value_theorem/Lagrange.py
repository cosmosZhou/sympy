from util import *
import axiom


@apply
def apply(*given):
    is_continuous, is_differentiable = given
    fz, (z, a, b) = axiom.is_continuous(is_continuous)
    _fz, (_z, _a, _b) = axiom.is_differentiable(is_differentiable)
    assert _fz == fz
    assert _z == z
    assert _a == a
    assert _b == b
    assert a < b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Exists[z:Interval(a, b, left_open=True, right_open=True)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus, sets
    from axiom.calculus.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    from axiom.calculus.integral.intermediate_value_theorem import is_continuous
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True))
    f = Function.f(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b))

    def g(x):
        return f(x) - (f(b) - f(a)) / (b - a) * x

    g = Function.g(eval=g)

    x = Symbol.x(real=True)
    Eq.g_definition = g(x).this.defun()

    Eq << Eq.g_definition.subs(x, a)

    Eq << Eq.g_definition.subs(x, b)

    Eq << Eq[-1] - Eq[-2]

    Eq.equal = Eq[-1].this.rhs.ratsimp()

    Eq.is_continuous = Eq[0]._subs(f, g).copy(plausible=True)

    Eq << Eq.is_continuous.this.function.lhs.expr.defun()

    Eq << Eq[-1].this.function.rhs.defun()

    Eq << Eq[-1].this.function.lhs.apply(calculus.limit.to.add)

    Eq << Eq[-1].this.function.lhs.args[0].apply(calculus.limit.to.mul)

    Eq.is_differentiable = Eq[1]._subs(f, g).copy(plausible=True)

    Eq << Eq.is_differentiable.this.function.lhs.expr.defun()

    Eq << Eq[-1].this.function.lhs.apply(calculus.derivative.to.add)

    Eq << Eq[-1].this.function.apply(sets.contains.given.contains.add, (f(b) - f(a)) / (b - a))

    Eq << calculus.is_continuous.is_differentiable.eq.imply.any_eq.Rolle.apply(Eq.is_continuous, Eq.is_differentiable, Eq.equal)

    Eq << Eq[-1].this.function.lhs.expr.defun()

    Eq << Eq[-1].this.function.lhs.apply(calculus.derivative.to.add)

    Eq << Eq[-1].this.function * (b - a)


if __name__ == '__main__':
    run()

