from util import *


@apply(given=None)
def apply(self, t):
    e, interval = self.of(Element)
    t = sympify(t)
    return Equivalent(self, Element(e + (-t), interval + (-t)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(integer=True)
    a, b, t = Symbol(real=True)

    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(sets.el.imply.el.sub, t)

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.el.add, t)


if __name__ == '__main__':
    run()

# created on 2018-04-12
