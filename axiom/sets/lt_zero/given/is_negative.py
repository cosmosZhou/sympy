from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)
    assert x.is_finite
    return Element(x, Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True)
    Eq << apply(x < 0)

    Eq << sets.el_interval.imply.lt.apply(Eq[1])










if __name__ == '__main__':
    run()
# created on 2020-04-25
