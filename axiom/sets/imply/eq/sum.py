from util import *


@apply
def apply(s, wrt=None):
    assert s.is_set
    if wrt is None:
        wrt = s.generate_var(**s.etype.dict)
    return Equal(Sum[wrt:s](Bool(Contains(wrt, s))), abs(s))


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(S)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.lhs().expr.simplify()


if __name__ == '__main__':
    run()

