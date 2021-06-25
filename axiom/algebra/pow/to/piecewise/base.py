from util import *


@apply
def apply(self):
    ecs, t = self.of(Piecewise ** Expr)
    return Equal(self, Piecewise(*((e ** t, c) for e, c in ecs)))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    A = Symbol.A(etype=dtype.real)
    x = Symbol.x(real=True)
    t = Symbol.t(real=True)
    g = Function.g(real=True)
    h = Function.h(real=True)
    Eq << apply(Pow(Piecewise((g(x), Contains(x, A)),(h(x), True)), t, evaluate=False))
    
    Eq << algebra.eq.given.ou.apply(Eq[0])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool)
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, invert=True)


if __name__ == '__main__':
    run()