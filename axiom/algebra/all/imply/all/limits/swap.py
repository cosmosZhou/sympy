from util import *
import axiom


@apply
def apply(given):
    from sympy.concrete.limits import limits_dependent
    fn, *limits = given.of(ForAll)
    assert len(limits) == 2
    limit_x, limit_y = limits

    limits = limit_y, limit_x

    assert not limits_dependent([limit_x], [limit_y])

    return ForAll(fn, *limits)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[x:g(x) > 0, y:g(y) > 0](f(x, y) > 0))

    Eq << algebra.all.imply.ou.apply(Eq[0])

    Eq << algebra.ou.imply.all.apply(Eq[-1], pivot=1, wrt=x)

    Eq << Eq[-1].this.function.apply(algebra.ou.imply.all, pivot=1, wrt=y)


if __name__ == '__main__':
    run()

