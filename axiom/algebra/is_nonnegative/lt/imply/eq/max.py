from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    _x, y = lt.of(Less)
    assert x == _x

    return Equal(Max(y ** 2, x ** 2), y ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x < y)

    Eq << algebra.lt.imply.le.relax.apply(Eq[1])

    Eq << algebra.is_nonnegative.le.imply.eq.max.apply(Eq[0], Eq[-1])

    

    

    


if __name__ == '__main__':
    run()