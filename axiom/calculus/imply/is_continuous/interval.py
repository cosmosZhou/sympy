from util import *


@apply
def apply(fx, limit, xi=None):
    x, *ab = limit
    if len(ab) == 2:
        domain = Interval(*ab)
    else:
        [domain] = ab
        
    assert fx.is_continuous(x, domain)
    if xi is None:
        xi = fx.generate_var(real=True, var='xi')

    return All[xi:domain](Equal(Limit[x:xi](fx), fx._subs(x, xi)))


@prove
def prove(Eq):
    from axiom import calculus

    f = Function(real=True, continuous=True)
    x, a, b = Symbol(real=True)
    Eq << apply(f(x), (x, a, b))

    Eq << Eq[0].this.find(Limit).apply(calculus.limit.to.expr.continuity)


if __name__ == '__main__':
    run()