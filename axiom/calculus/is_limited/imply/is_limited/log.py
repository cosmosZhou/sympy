from util import *


@apply
def apply(is_limited):
    from axiom.calculus.is_limited.imply.any_all.limit_definition import of_limited
    fx, (x, x0, dir) = of_limited(is_limited, positive=True)
    return Element(Limit[x:x0:dir](log(fx)), Reals)


@prove(proved=False)
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Interval(0, oo, left_open=True)))

    epsilon, epsilon0, delta0 = Symbol(positive=True)
    Eq << calculus.is_limited.imply.any_all.limit_definition.symbol_subs.apply(Eq[0], epsilon0, delta0, var='A')

    A = Eq[-1].expr.expr.find(Add[-~Symbol])
    Eq.is_limited = A.this.definition.reversed

    Eq << Eq[0].subs(Eq.is_limited)

    Eq << sets.el.imply.is_positive.apply(Eq[-1])

    Eq << algebra.is_positive.eq.imply.eq.log.apply(Eq[-1], Eq.is_limited)


if __name__ == '__main__':
    run()
