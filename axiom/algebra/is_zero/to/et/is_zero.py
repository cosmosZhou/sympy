from util import *


@apply(given=None)
def apply(self):
    z = self.of(Equal[0])
    x = Re(z)
    y = Im(z)
    return Equivalent(self, Equal(x, 0) & Equal(y, 0))


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Equal(z, 0))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.lhs.apply(algebra.expr.to.add.complex)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.imply.eq.pow, exp=2)

    Eq << Eq[-1].this.lhs.apply(algebra.add_is_zero.imply.et.is_zero)

    Eq << Eq[2].this.rhs.lhs.apply(algebra.expr.to.add.complex)
    Eq << algebra.suffice_et.given.suffice.subs.apply(Eq[-1], 0)


if __name__ == '__main__':
    run()