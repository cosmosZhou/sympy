from util import *


@apply
def apply(given, factor):
    assert factor < 0
    x = given.of(Expr < 0)

    return Greater(x * factor, 0)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    h = Symbol(real=True, shape=(n,))
    a = Symbol(real=True, negative=True)
    Eq << apply(h[k] < 0, a)

    Eq << Less(a, 0, plausible=True)

    Eq << algebra.lt_zero.lt_zero.imply.gt_zero.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-01-20
