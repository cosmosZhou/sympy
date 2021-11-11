from util import *


@apply
def apply(self):
    a, b = self.of(FiniteSet & FiniteSet)
    return Equal(self, Piecewise((a.set, Equal(a, b)), (a.emptySet, True)))

@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(integer=True)
    Eq << apply(a.set & b.set)

    Eq << algebra.eq.given.ou.apply(Eq[0])
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.eq)


if __name__ == '__main__':
    run()
# created on 2018-09-11
# updated on 2018-09-11
