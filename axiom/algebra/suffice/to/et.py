from util import *
import axiom



@apply(given=None)
def apply(self):
    p, q = self.of(Suffice)

    return Equivalent(self, And(*(Suffice(p, eq) for eq in q.of(And))), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    h = Function.h(integer=True)

    Eq << apply(Suffice(x > y, (f(x) > g(y)) & (h(x) > g(y))))

    Eq << algebra.equivalent.given.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.suffice.imply.suffice.split.et)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.given.suffice.split.et)

if __name__ == '__main__':
    run()
