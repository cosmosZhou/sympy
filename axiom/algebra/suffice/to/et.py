from util import *



@apply(given=None)
def apply(self):
    p, q = self.of(Suffice)

    return Equivalent(self, And(*(Suffice(p, eq) for eq in q.of(And))), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, g, h = Function(integer=True)
    Eq << apply(Suffice(x > y, (f(x) > g(y)) & (h(x) > g(y))))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.suffice.imply.et.suffice)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.given.et.suffice)


if __name__ == '__main__':
    run()
