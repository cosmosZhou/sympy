from util import *


@apply
def apply(self): 
    expr, (x, x0, dir) = self.of(Limit)
    args = expr.of(Mul)
    
    coefficient = []
    factors = []
    for arg in args:
        if arg._has(x):
            factors.append(arg)
        else:
            coefficient.append(arg)
    
    coefficient = Mul(*coefficient)
    factors = Mul(*factors)
    
    limited = Limit[x:x0:dir](factors).simplify()
    return Equal(self, coefficient * limited)


@prove
def prove(Eq):
    from axiom import calculus, algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True, zero=False)
    x0 = Symbol.x0(real=True)
    f = Function.f(real=True)
    Eq << apply(Limit[x:x0](f(x) * y))

    A = Symbol.A(Eq[0].rhs.args[1], real=True)
    Eq << A.this.definition

    epsilon = Symbol.epsilon(positive=True)
    delta = Symbol.delta(positive=True)
    Eq << calculus.eq.imply.any_all.limit_definition.apply(Eq[1], epsilon=epsilon, delta=delta)

    Eq << Eq[-1].this.find(Less) * abs(y)

    Eq << Eq[-1].subs(epsilon, epsilon / abs(y))

    Eq.lhs = Equal(Eq[0].lhs, A * y, plausible=True)

    Eq << Eq.lhs.this.apply(calculus.eq.to.any_all.limit_definition, epsilon=epsilon, delta=delta)

    Eq << Eq[-1].this.expr.expr.find(Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Abs[Mul]).apply(algebra.abs.to.mul)

    Eq << Eq[-1].this.find(Mul[~Abs[Add]]).apply(algebra.abs.neg)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.lhs, Eq[1] * y)


if __name__ == '__main__':
    run()
