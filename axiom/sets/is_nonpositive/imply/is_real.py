from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    return Element(x, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(complex=True)
    Eq << apply(x <= 0)
    Eq << sets.le.imply.is_real.apply(Eq[0])


if __name__ == '__main__':
    run()
