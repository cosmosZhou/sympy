from util import *


@apply
def apply(x, d=1, evaluate=False):
    d = sympify(d)
    assert d.is_integer and d > 0
    assert x.is_integer
    return GreaterEqual(Floor(x / d) * d, x - d + 1, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)

    Eq << apply(x, d)

    Eq << algebra.imply.gt.floor.apply(x / d)

    Eq << Eq[-1] * d

    Eq << Eq[-1].this.rhs.expand()

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-05-27
# updated on 2018-05-27
