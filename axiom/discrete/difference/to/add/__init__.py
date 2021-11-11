from util import *


@apply
def apply(self):
    [*args], *variable_count = self.of(Difference[Add])

    rhs = Add(*(Difference(arg, *variable_count).simplify() for arg in args))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    f, g = Function(real=True)
    x = Symbol(real=True)
    d = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Difference(f(x) + g(x), x, d))

    Eq.initial = Eq[0].subs(d, 1)

    Eq << Eq.initial.this.lhs.apply(discrete.difference.to.add.one)

    Eq.induct = Eq[0].subs(d, d + 1)

    Eq << discrete.eq.imply.eq.difference.apply(Eq[0], (x, 1))

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.apply(discrete.difference.to.add.one)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq[-1], n=d, start=1)


if __name__ == '__main__':
    run()

from . import one
# created on 2020-10-09
# updated on 2020-10-09
