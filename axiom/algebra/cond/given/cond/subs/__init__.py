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

    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    S = Symbol.S(etype=dtype.real * (m, n))
    Eq << apply(Contains(a * b, S), given=Equal(a, 2 * c))

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[1].reversed, Eq[2])


if __name__ == '__main__':
    run()
from . import cond
from . import bool
