from util import *



@apply
def apply(given, d):
    lhs, rhs = given.of(Unequal)
    return Unequal(lhs / d, rhs / d) | Equal(d, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, d = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, y), d)

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.ne_zero.eq.imply.eq.mul)

    Eq <<= ~Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-02-06
