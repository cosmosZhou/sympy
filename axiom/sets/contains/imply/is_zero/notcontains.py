from util import *



@apply
def apply(given):
    return Equal(Bool(given.invert()), 0)


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

