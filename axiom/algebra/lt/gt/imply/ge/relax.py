from util import *


@apply
def apply(lt, gt):
    a, x = lt.of(Less)
    b, _x = gt.of(Greater)
    if x != _x:
        b, _x, a, x = x, a, _x, b
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a < x, b > x)

    Eq << algebra.lt.gt.imply.gt.transit.apply(Eq[0], Eq[1])
    Eq << algebra.gt.imply.ge.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-10-12
# updated on 2018-10-12
