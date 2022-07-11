from util import *


@apply
def apply(self):
    args = self.of(Sin[Piecewise])
    ecs = [(Sin(e), c) for e, c in args]
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    from axiom import algebra
    
    x = Symbol(real=True)
    A = Symbol(etype=dtype.real)
    f, g = Function(real=True)
    Eq << apply(Sin(Piecewise((f(x), Element(x, A)), (g(x), True))))
    
    Eq << algebra.eq.given.ou.apply(Eq[0])
    
    Eq << Eq[-1].this.find(And).apply(algebra.et.given.et.subs.bool)
    
    Eq << Eq[-1].this.find(And).apply(algebra.et.given.et.subs.bool, invert=True)


if __name__ == '__main__':
    run()
# created on 2022-01-20
