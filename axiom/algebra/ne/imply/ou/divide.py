from util import *
import axiom



@apply
def apply(given, d):
    lhs, rhs = given.of(Unequal)
    return Unequal(lhs / d, rhs / d) | Equal(d, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    d = Symbol.d(real=True, given=True)
    Eq << apply(Unequal(x, y), d)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.is_nonzero.eq.imply.eq.multiply)

    Eq <<= ~Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
