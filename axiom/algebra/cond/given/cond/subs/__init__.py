from util import *


@apply
def apply(f_eq, *, given=None, reverse=False, simplify=True, assumptions={}):
    from axiom.algebra.all_eq.cond.imply.all.subs import subs
    lhs, rhs = given.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
    return subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions)


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real * (m, n))
    Eq << apply(Element(a * b, S), given=Equal(a, 2 * c))

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[1].reversed, Eq[2])


if __name__ == '__main__':
    run()
from . import cond
from . import bool
