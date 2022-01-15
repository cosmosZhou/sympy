from util import *


@apply
def apply(given, M=None):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert b >= a
    if M is None:
        M = given.generate_var(real=True, var='M')
    return Any[M](All[z:a:b](f <= M))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval(a, oo, left_open=True))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << calculus.is_continuous.imply.any_all_le.extreme_value_theorem.apply(Eq[0])

    Eq << algebra.any.imply.any.limits.relax.apply(Eq[-1], domain=Reals)

    m = Eq[1].variable
    Eq << algebra.any.given.any.subs.apply(Eq[1], m, f(Eq[-1].variable))


if __name__ == '__main__':
    run()
# created on 2020-06-14
