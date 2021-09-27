from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Element)
    if rhs in S:
        rhs = S
    else:
        rhs |= S
    return Element(lhs, rhs)


@prove
def prove(Eq):
    from axiom import sets, algebra

    e = Symbol(integer=True)
    U, S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, U), S)

    Eq << sets.el.given.ou.split.union.apply(Eq[1])

    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()


from . import interval
