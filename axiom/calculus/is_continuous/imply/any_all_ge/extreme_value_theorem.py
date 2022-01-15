from util import *


@apply
def apply(given):
    ((f, (z, xi, direction)), _f), (_xi, a, b) = given.of(All[Equal[Limit]])
    assert direction == 0
    assert xi == _xi
    assert _f == f._subs(z, xi)
    assert b >= a
    return Any[xi:a:b](All[z:a:b](f >= _f))


@prove
def prove(Eq):
    from axiom import calculus

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval(a, oo, left_open=True))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all_any_eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()
# created on 2020-06-13
