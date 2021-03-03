from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre
from sympy.concrete.limits import limits_union


@apply
def apply(*given):
    exists_forall, forall = given
    forall0, *limits_e = axiom.is_Exists(exists_forall)
    
    cond, *limits_f0 = axiom.is_ForAll(forall0)
    _cond, *limits_f1 = axiom.is_ForAll(forall)
    assert forall0.variables == forall.variables
    assert _cond == _cond
    
    limits_f = limits_union(limits_f0, limits_f1)
    return Exists(ForAll(cond, *limits_f), *limits_e)


@prove
def prove(Eq):
    N = Symbol.N(integer=True)
    g = Function.g(shape=(), integer=True)
    M = Symbol.M(g(N))
    n = Symbol.n(integer=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    f = Function.f(shape=(), integer=True)
    Eq << apply(Exists[N](ForAll[n:N:oo](f(n) <= M)), ForAll[n:N](f(n) <= M))
    
    Eq << Eq[1].this.function.apply(algebre.forall.forall.imply.forall.limits_union, Eq[2], depth=0)

    
if __name__ == '__main__':
    prove(__file__)
