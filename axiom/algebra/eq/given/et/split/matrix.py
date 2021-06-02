from util import *

import axiom


@apply
def apply(given):
    lhs, rhs = given.of(Equal)

    assert lhs.is_Matrix and rhs.is_Matrix

    args = [Equal(lhs, rhs).simplify() for lhs, rhs in zip(lhs._args, rhs._args)]
    return And(*args)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    Eq << apply(Equal(Matrix([a, b]), Matrix([c, d])))

    Eq << algebra.et.imply.conds.apply(Eq[1])

    Eq << Eq[0].this.lhs.subs(Eq[-2]).subs(Eq[-1])


if __name__ == '__main__':
    run()

