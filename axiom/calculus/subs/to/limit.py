from util import *


@apply
def apply(self):
    (fx, (x, d)), [_x], [xi] = self.of(Subs[Derivative])
    assert d == 1
    assert x == _x
    
    return Equal(self, Limit[x:xi]((fx - fx._subs(x, xi)) / (x - xi)))

    
@prove
def prove(Eq):
    from axiom import calculus

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True, given=True)
    f = Function.f(real=True)
    epsilon = Symbol.epsilon(real=True)
    Eq << apply(Subs(Derivative(f(x), x), x, x0))

    Eq << Eq[0].this.rhs.apply(calculus.limit.limits.offset, x0)

    t = Symbol.t(real=True)
    Eq << Derivative(f(t), t).this.apply(calculus.derivative.to.limit)

    Eq << Eq[-1].this.rhs.apply(calculus.limit.limits.subs, x)
    Eq << Eq[-1].subs(t, x0)


if __name__ == '__main__':
    run()