from util import *


@apply(given=None)
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    return Equivalent(self, associate(All, self, simplify=simplify))


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    f = Function.f(real=True)
    h = Function.h(real=True)
    Eq << apply(All[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all_et.imply.et.all)

    Eq << Eq[-1].this.rhs.apply(algebra.all_et.given.et.all)


if __name__ == '__main__':
    run()

from . import doit, split
