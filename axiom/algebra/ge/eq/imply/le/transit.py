from util import *



@apply
def apply(b_greater_than_x, x_eq_a):
    b, x = b_greater_than_x.of(GreaterEqual)
    _x, a = x_eq_a.of(Equal)
    assert x == _x
    return LessEqual(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b >= x, Equal(x, a))

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)


if __name__ == '__main__':
    run()
# created on 2019-05-16
