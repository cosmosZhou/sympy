from util import *


@apply(given=None)
def apply(self, t):
    e, interval = self.of(Element)

    return Equivalent(self,Element(e + t, interval + t))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.el.add, t), Eq[-1].this.lhs.apply(sets.el.given.el.add, t)


if __name__ == '__main__':
    run()
# created on 2020-02-27
# updated on 2020-02-27
