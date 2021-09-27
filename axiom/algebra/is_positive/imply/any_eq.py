from util import *


@apply
def apply(given, var=None):
    x = given.of(Expr > 0)
    if var is None:
        var = given.generate_var(positive=True)
    else:
        assert not var.is_given
        assert var.domain == Interval(0, oo, left_open=True)
    return Any[var](Equal(x, var))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[0])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << algebra.any.given.cond.subs.apply(Eq[1], Eq[1].variable, abs(x))

    Eq << algebra.et.given.et.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
