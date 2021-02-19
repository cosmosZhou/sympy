from axiom.utility import prove, apply
from sympy import *
from axiom import algebre


@apply
def apply(given):
    assert given.is_ForAll
    limits = given.limits
    assert len(limits) == 1
    
    limit = limits[0][0], given.function.invert()
    
    return ForAll(given.limits_condition.invert().simplify(), limit)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)
    g = Function.g(nargs=(), shape=(), integer=True)

    Eq << apply(ForAll[e:g(e) > 0](f(e) > 0))
    
    Eq << algebre.forall.imply.ou.rewrite.apply(Eq[0])
    
    Eq << algebre.ou.imply.forall.apply(Eq[-1], pivot=0, wrt=e)


if __name__ == '__main__':
    prove(__file__)

