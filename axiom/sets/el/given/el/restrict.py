from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Element)
    if S in rhs:
        rhs = S
    else:
        rhs &= S
    return Element(lhs, rhs)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True)
    U, S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, U), S)

    Eq << sets.el_intersect.imply.et.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
