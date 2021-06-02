from util import *
import axiom



@apply(given=None)
def apply(self):
    p, q = self.of(Suffice)
    return Equivalent(self, Suffice(q.invert(), p.invert()))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Suffice(x > y, f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(algebra.suffice.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.suffice.to.ou)

if __name__ == '__main__':
    run()

#     https://en.wikipedia.org/wiki/Contraposition
