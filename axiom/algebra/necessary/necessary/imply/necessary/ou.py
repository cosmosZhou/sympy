from util import *
import axiom



@apply
def apply(*given):
    x_imply_P, y_imply_P = given
    p, x = x_imply_P.of(Necessary)
    q, y = y_imply_P.of(Necessary)

    return Necessary(p | q, x | y)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Necessary(a > 0, x > 0), Necessary(b > 0, y > 0))

    Eq << Eq[2].reversed

    Eq << algebra.suffice.suffice.imply.suffice.ou.apply(Eq[0].reversed, Eq[1].reversed)


if __name__ == '__main__':
    run()
