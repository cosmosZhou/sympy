from util import *
import axiom



@apply
def apply(*given):
    b_greater_than_x, x_eq_a = given
    b, x = b_greater_than_x.of(Greater)
    _x, a = x_eq_a.of(Equal)
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, Equal(x, a))

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.gt.simplify.common_terms)


if __name__ == '__main__':
    run()
