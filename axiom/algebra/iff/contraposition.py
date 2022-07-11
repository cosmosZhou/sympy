from util import *


@apply(given=None)
def apply(self):
    p, q = self.of(Equivalent)
    return Equivalent(self, Equivalent(q.invert(), p.invert()))


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Equivalent(p, q))

    Eq << Eq[0].this.lhs.apply(algebra.iff.to.ou.et)

    Eq << Eq[-1].this.rhs.apply(algebra.iff.to.ou.et)


if __name__ == '__main__':
    run()
# created on 2022-01-27
