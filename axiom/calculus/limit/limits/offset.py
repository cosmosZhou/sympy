from util import *


@apply
def apply(self, offset):     
    fx, (x, x0, dir) = self.of(Limit)    
    fx = fx._subs(x, x + offset)
    
    return Equal(self, Limit[x:x0 - offset:dir](fx))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Limit[x:x0](f(x - x0)), x0)

    #we assume this limit exists and is real
    A = Symbol.A(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(algebra.all.imply.all.limits.subs.offset, -x0)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()