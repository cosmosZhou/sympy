from util import *


@apply
def apply(given, wrt=None, index=0):
    [*s] = given.of(Unequal[Intersection, EmptySet])

    A = s.pop(index)
    B = Intersection(*s)

    if wrt is None:
        wrt = B.element_symbol(A.free_symbols)

    return Any[wrt:B](Element(wrt, A))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A & B, A.etype.emptySet))

    Eq << sets.imply.ou.el.apply(A & B)

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el_intersect.imply.et, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], index=1, simplify=None)


if __name__ == '__main__':
    run()

# created on 2018-09-07
