from util import *



@apply
def apply(*given):
    a_less_than_x, b_eq_x = given
    a, x = a_less_than_x.of(Less)
    b, _x = b_eq_x.of(Equal)
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a < x, Equal(b, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.apply(algebra.gt.simplify.common_terms)


if __name__ == '__main__':
    run()
