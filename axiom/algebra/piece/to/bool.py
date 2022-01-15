from util import *


@apply
def apply(self):
    (one, cond), (zero, S[True]) = self.of(Piecewise)
    if zero:
        assert zero == 1
        assert one == 0
        cond = cond.invert()
    return Equal(self, Bool(cond))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Piecewise((0, x > y), (1, True)))

    Eq << Eq[0].this.rhs.apply(algebra.bool.to.piece)
    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)





if __name__ == '__main__':
    run()
# created on 2021-12-16
