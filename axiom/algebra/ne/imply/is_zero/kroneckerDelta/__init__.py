from util import *


@apply(simplify=False)
def apply(given):
    lhs, rhs = given.of(Unequal)
    return Equal(KroneckerDelta(lhs, rhs), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << Eq[1].this.lhs.apply(algebra.kroneckerDelta.to.piece)


if __name__ == '__main__':
    run()

from . import mul
