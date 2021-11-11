from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    y, _x = lt.of(Less)
    assert x == _x

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y < x)

    Eq << algebra.lt.imply.le.relax.apply(Eq[1])

    Eq << algebra.le_zero.le.imply.eq.min.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-12-09
# updated on 2019-12-09
