from util import *
import axiom



@apply
def apply(*given):
    x_less_than_a, y_less_than_a = given
    x, a = x_less_than_a.of(Less)
    y, _a = y_less_than_a.of(Less)
    assert a == _a
    return Less(Max(x, y), a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x < a, y < a)

    Eq << Eq[-1].this.lhs.astype(Piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[-1], invert=True)

    Eq << algebra.cond.cond.imply.cond.apply(Eq[1], Eq[-1], invert=True)



if __name__ == '__main__':
    run()
