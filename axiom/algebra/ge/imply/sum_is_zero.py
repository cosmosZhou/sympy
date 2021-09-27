from util import *


@apply
def apply(ge, sgm):
    _a, _b = ge.of(GreaterEqual)
    expr, (k, a, b) = sgm.of(Sum)
    assert _a == a and _b == b
    return Equal(sgm, 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True, given=True)
    n = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(a >= b, Sum[n:a:b](f(n)))

    Eq << Eq[-1].this.lhs.apply(algebra.sum.bool)

    Eq << sets.ge.imply.range_is_empty.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()