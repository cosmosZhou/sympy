from util import *



@apply
def apply(given):
    assert given.is_All
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(All[x:A](Contains(f(x), s)))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

