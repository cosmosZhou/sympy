from util import *


@apply
def apply(is_positive, lt):
    x = is_positive.of(Expr > 0)
    _x, M = lt.of(Less)
    assert x == _x

    return Less(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x > 0, x < M)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << algebra.ge_zero.lt.imply.lt.square.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-28
# updated on 2019-08-28
