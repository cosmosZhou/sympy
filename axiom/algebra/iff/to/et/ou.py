from util import *


@apply(given=None)
def apply(self):
    p, q = self.of(Equivalent)
    return Equivalent(self, (p.invert() | q) & (q.invert() | p), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    p, q = Symbol(bool=True)
    Eq << apply(Equivalent(p, q))

    Eq << Eq[0].this.lhs.apply(algebra.iff.to.et.infer)

    Eq << Eq[-1].this.find(Infer).apply(algebra.infer.to.ou)

    Eq << Eq[-1].this.find(Infer).apply(algebra.infer.to.ou)


if __name__ == '__main__':
    run()
# created on 2022-01-27
