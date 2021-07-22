from util import *


@apply
def apply(self, y):
    fx, (x, x0, dir) = self.of(Limit)
    assert not self._has(y)
    assert y.is_symbol and not y.is_given
    fy = fx._subs(x, y)
    
    return Equal(self, Limit[y:x0:dir](fy))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Limit[x:x0](f(x)), y)

    #we assume this limit exists and is real
    A = Symbol.A(Eq[0].rhs, real=True)
    Eq << A.this.definition

    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.expr.limits_subs(Eq[-1].expr.variable, x)

    Eq << calculus.any_all.imply.eq.limit_definition.apply(Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()