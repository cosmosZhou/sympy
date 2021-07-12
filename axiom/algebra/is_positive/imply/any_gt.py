from util import *


@apply
def apply(given, var=None):
    x = given.of(Expr > 0)
    if var is None:
        var = given.generate_var(positive=True)
    else:
        assert not var.is_given
        assert var.domain == Interval(0, oo, left_open=True)
    return Any[var](Greater(x, var))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(x > 0)

    Eq << algebra.any.given.cond.subs.apply(Eq[1], Eq[1].variable, x / 2)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[0] / 2

    Eq << algebra.gt.given.is_positive.apply(Eq[-2])


if __name__ == '__main__':
    run()