from util import *


def find_denominator(expr):
    if expr.is_Pow:
        e = expr.exp
        if e < 0:
            if e.is_rational:
                return expr.base
        return

    if expr.is_Mul or expr.is_Add:
        for arg in expr.args:
            den = find_denominator(arg)
            if den is not None:
                return den


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    den = find_denominator(lhs)
    if den is None:
        den = find_denominator(rhs)

    return Unequal(den, 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d = Symbol(complex=True)
    Eq << apply(Equal(a / b + d, c))

    Eq << Eq[0].this.apply(algebra.eq.transport, lhs=0)

    Eq << algebra.eq.imply.ne_zero.domain_definition.st.mul.apply(Eq[-1])





if __name__ == '__main__':
    run()

from . import st
# created on 2019-04-15
# updated on 2022-04-02
