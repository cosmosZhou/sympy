from util import *


@apply
def apply(self):
    b, ecs = self.of(Expr ** Piecewise)
    return Equal(self, Piecewise(*((b ** e, c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    A = Symbol(etype=dtype.real)
    x, b = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(b ** Piecewise((g(x), Element(x, A)),(h(x), True)))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)


if __name__ == '__main__':
    run()
# created on 2018-04-13
# updated on 2018-04-13
