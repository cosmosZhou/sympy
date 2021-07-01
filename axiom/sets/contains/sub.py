from util import *


@apply(given=None)
def apply(self, t):
    e, interval = self.of(Contains)
    t = sympify(t)
    return Equivalent(self, Contains(e + (-t), interval + (-t)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)

    Eq << apply(Contains(x, Interval(a, b)), t)

    Eq << algebra.equivalent.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.contains.sub, t)

    Eq << Eq[-1].this.rhs.apply(sets.contains.imply.contains.add, t)


if __name__ == '__main__':
    run()

