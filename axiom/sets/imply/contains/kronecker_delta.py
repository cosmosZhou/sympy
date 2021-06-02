from util import *

import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    assert self.is_KroneckerDelta
    return Contains(self, {0, 1})


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.astype(Piecewise)

    Eq << sets.imply.contains.bool.apply(Bool(Equal(x, y)))

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

