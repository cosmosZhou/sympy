from util import *


@apply(given=None)
def apply(self, simplify=True):
    from axiom.algebra.sum.to.add import associate
    assert self.is_ForAll
    return Equivalent(self, associate(self, simplify=simplify))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)

    f = Function.f(real=True)
    h = Function.h(real=True)
    Eq << apply(ForAll[i:n]((f(i) > 0) & (h(i) > 0)))

    Eq << algebra.equivalent.given.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.all_et.imply.et)

    Eq << Eq[-1].this.rhs.apply(algebra.all_et.given.et)


if __name__ == '__main__':
    run()

from . import doit, dissect
