from util import *

import axiom


@apply
def apply(given):
    lhs, rhs = given.of(Equal)

    assert lhs.is_FiniteSet
    args = [Contains(lhs, rhs).simplify() for lhs in lhs.args]

    return And(*args)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    S = Symbol.S(etype=dtype.real)
    Eq << apply(Equal({a, b}, S))

    Eq << algebra.et.given.conds.apply(Eq[1])

    Eq << Contains(a, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Contains(b, {a, b}, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

if __name__ == '__main__':
    run()

