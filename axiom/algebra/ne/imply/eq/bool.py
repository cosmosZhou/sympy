from util import *



@apply
def apply(given):
    assert given.is_Unequal
    return Equal(Bool(given), 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    y = Symbol.y(real=True)

    Eq << apply(Unequal(f(x), y))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

