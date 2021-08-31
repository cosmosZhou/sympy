from util import *


@apply
def apply(f_eq, *, given=None, reverse=False, simplify=True, assumptions={}):
    lhs, rhs = given.of(Equivalent)
    if reverse:
        lhs, rhs = rhs, lhs
    return f_eq._subs(lhs, rhs, simplify=simplify, assumptions=assumptions)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f = Function(integer=True)
    Eq << apply(Equal(Piecewise((f(a), Element(a, A)), (f(b), True)), 0), given=Equivalent(Element(a, A), Element(b, B)))

    Eq << algebra.equivalent.cond.imply.cond.subs.apply(Eq[1].reversed, Eq[2])


if __name__ == '__main__':
    run()