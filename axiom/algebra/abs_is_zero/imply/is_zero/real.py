from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.piece)

    Eq << algebra.eq_piece.imply.ou.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
