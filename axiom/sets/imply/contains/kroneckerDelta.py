from util import *


@apply
def apply(self):
    assert self.is_KroneckerDelta
    return Contains(self, {0, 1})


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(algebra.kroneckerDelta.to.piecewise)

    Eq << sets.imply.contains.bool.apply(Bool(Equal(x, y)))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

