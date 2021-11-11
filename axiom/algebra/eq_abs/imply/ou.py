from util import *


@apply
def apply(given):
    abs_x, y = given.of(Equal)
    if not abs_x.is_Abs:
        abs_x, y = y, abs_x

    x = abs_x.of(Abs)
    assert x.is_real

    return Or(Equal(x, y), Equal(x, -y))


@prove
def prove(Eq):
    from axiom import algebra
    x, a = Symbol(real=True, given=True)
    Eq << apply(Equal(abs(x), a))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.piece)

    Eq << algebra.eq_piece.imply.ou.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << algebra.et.imply.ou.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2019-04-21
# updated on 2019-04-21
