from util import *


@apply
def apply(x, negate=False):
    if negate:
        x = -x
    return LessEqual(x, abs(x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)

    Eq << apply(x)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=x > 0)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.args[0].apply(algebra.is_positive.imply.eq.abs)

    Eq << Eq[-1].apply(algebra.gt.eq.imply.gt.transit)


if __name__ == '__main__':
    run()

del add
from . import add
from . import substract
