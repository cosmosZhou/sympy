from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given, *limits):
    lhs, rhs = axiom.is_StrictLessThan(given)
    
    return StrictLessThan(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)
    
    Eq << apply(StrictLessThan(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebre.condition.imply.forall.minify, (i, 0, n))
    
    Eq << algebre.forall_strict_less_than.imply.strict_less_than.sum.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

