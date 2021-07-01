from util import *


@apply
def apply(self):
    b, ecs = self.of(Expr ** Piecewise)    
    return Equal(self, Piecewise(*((b ** e, c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True)
    A = Symbol.A(etype=dtype.real)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    Eq << apply(b ** Piecewise((g(x), Contains(x, A)),(h(x), True)))

    Eq << algebra.eq.given.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)


if __name__ == '__main__':
    run()