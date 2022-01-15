from util import *


@apply(given=None)
def apply(self):
    q, p = self.of(Assuming)
    return Equivalent(self, Assuming(p.invert(), q.invert()))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Assuming(x > y, f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(algebra.assuming.to.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.assuming.to.ou)


if __name__ == '__main__':
    run()
# created on 2019-03-02
