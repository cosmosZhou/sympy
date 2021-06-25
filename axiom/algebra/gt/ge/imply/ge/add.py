from util import *



@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(Greater)
    b, y = x_less_than_b.of(GreaterEqual)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(a > x, y >= b)

    Eq << algebra.gt.ge.imply.gt.add.apply(Eq[0], Eq[1])

    Eq << algebra.gt.imply.ge.relax.apply(Eq[-1])



if __name__ == '__main__':
    run()
