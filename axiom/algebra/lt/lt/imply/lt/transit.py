from util import *
import axiom



@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(Less)
    _x, b = x_less_than_b.of(Less)
    if b == a:
        a, x, _x, b = _x, b, a, x
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a < x, x < b)

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(algebra.lt.simplify.common_terms)

if __name__ == '__main__':
    run()
