from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given): 
    is_nonzero, forall_is_nonzero = given
    fa = axiom.is_nonzero(is_nonzero)
    fn1, limits = axiom.forall_is_nonzero(forall_is_nonzero)    
    n, fn, baseset = axiom.limit_is_nonzero_baseset(limits)
    
    assert fn._subs(n, n + 1) == fn1
    a = axiom.is_Interval(baseset, integer=True, end=oo)
    assert fn._subs(n, a) == fa
    
    return ForAll[n:a:oo](Unequal(fn, 0))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)    
    a = Symbol.a(integer=True)
    f = Function.f(nargs=(), shape=())
    Eq << apply(Unequal(f(a), 0), ForAll[n:Unequal(f(n), 0):Interval(a, oo, integer=True)](Unequal(f(n + 1), 0)))   

    g = Function.g(nargs=(), shape=(), eval=lambda x: f(x + a))
    
    Eq.g_definition = g(n).this.definition
    
    Eq << Eq.g_definition.subs(n, 0)
    
    Eq.g0_definition = Eq[0].subs(Eq[-1].reversed)
    
    Eq << Eq[1].subs(n, n + a)
    
    Eq << Eq[-1].subs(Eq.g_definition.reversed)
    
    Eq << Eq.g_definition.subs(n, n + 1)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    _n = Symbol.n(integer=True, nonnegative=True, given=False)
    Eq << Eq[-1].subs(n, _n)
    
    Eq << algebre.ou.imply.sufficient.apply(Eq[-1], pivot=1)

    Eq << algebre.is_nonzero.sufficient.imply.is_nonzero.induction.apply(Eq.g0_definition, Eq[-1], n=_n)
    
    Eq << Eq[-1].forall((_n,))
    
    Eq << Eq[-1].this.function.lhs.definition
    
    Eq << Eq[-1].limits_subs(n, n - a)

    
if __name__ == '__main__':
    prove(__file__)
