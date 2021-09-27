from util import *


@apply
def apply(self):
    ecs, t = self.of(Piecewise ** Expr)
    return Equal(self, Piecewise(*((e ** t, c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True)
    A = Symbol(etype=dtype.real)
    x, t = Symbol(real=True)
    g, h = Function(real=True)
    Eq << apply(Pow(Piecewise((g(x), Element(x, A)),(h(x), True)), t, evaluate=False))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)


if __name__ == '__main__':
    run()
