from util import *


@apply
def apply(given):
    is_nonzero, eq = given.of(And)
    if not eq.is_Equal:
        is_nonzero, eq = eq, is_nonzero
    x = is_nonzero.of(Unequal[0])
    a, b = eq.of(Equal)
    return is_nonzero, Equal((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(Equal(1 / x + y, z) & Unequal(x, 0))

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[1], Eq[2])
    Eq << Eq[-1].this.lhs.ratsimp()

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-05-02
