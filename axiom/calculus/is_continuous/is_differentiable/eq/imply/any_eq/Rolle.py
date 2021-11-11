from util import *


@apply
def apply(is_continuous, is_differentiable, equal):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_continuous, of_differentiable
    fz, (z, a, b) = of_continuous(is_continuous)
    _fz, (_z, _a, _b) = of_differentiable(is_differentiable)
    assert _fz == fz
    assert _z == z
    assert _a == a
    assert _b == b
    assert a < b
    fa, fb = equal.of(Equal)
    assert fz._subs(z, a) == fa
    assert fz._subs(z, b) == fb

    return Any[z:Interval(a, b, left_open=True, right_open=True)](Equal(Derivative(fz, z), 0))


@prove
def prove(Eq):
    from axiom import calculus

    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    from axiom import calculus
    a = Symbol(real=True)
    b = Symbol(domain=Interval(a, oo, left_open=True))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))

    Eq << Less(a, b, plausible=True)

    Eq << calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle.apply(Eq[-1], Eq[0], Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-06-16
# updated on 2020-06-16
