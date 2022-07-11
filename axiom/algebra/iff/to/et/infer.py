from util import *


@apply(given=None)
def apply(self):
    p, q = self.of(Equivalent)
    return Equivalent(self, And(Infer(p, q), Infer(q, p)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Equivalent(p, q))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.rhs.apply(algebra.infer.infer.given.iff)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.infer.imply.iff)


if __name__ == '__main__':
    run()
# created on 2022-01-27
