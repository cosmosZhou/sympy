from util import *


@apply
def apply(fx, limit, xi=None):
    x, a, b = limit
    assert fx.is_continuous(x)
    if xi is None:
        xi = fx.generate_var(real=True, var='xi')

    return All[xi:a:b](Equal(Limit[x:xi](fx), fx._subs(x, xi)))


@prove
def prove(Eq):
    from axiom import calculus

    f = Function(real=True, continuous=True)
    x, a, b = Symbol(real=True)
    Eq << apply(f(x), (x, a, b))

    
    Eq << Eq[0].this.find(Limit).apply(calculus.limit.to.expr.continuity)

    


if __name__ == '__main__':
    run()