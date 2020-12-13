from axiom.utility import plausible
from sympy.core.relational import Equal
from sympy import Symbol, Wild

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Or
import axiom
from axiom import algebre
from sympy.core.sympify import sympify
from sympy.core.function import Function


@plausible
def apply(*given, n=None, x=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    axiom.is_Equal(f0)
    fn_and_fnt, fn1 = axiom.is_Sufficient(sufficient)
    
    fn, fnt = axiom.is_And(fn_and_fnt)
    
    if fn1._subs(n, n - 1) == fnt:
        fn, fnt = fnt, fn
        
    assert fn1._subs(n, n - 1) == fn
    
    assert fn._subs(x, x + 1) == fnt
    assert fn._subs(n, start) == f0

    assert n.domain.min() == start
    
    return fn & fnt


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    x = Symbol.x(real=True)
    
    Eq << apply(Equal(f[0](x), g[0](x)), Sufficient(Equal(f[n](x), g[n](x)) & Equal(f[n](x + 1), g[n](x + 1)), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)
    
    Eq.initial = Eq[2].subs(n, 0)
    
    Eq << Eq[0].subs(x, x + 1)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq.induction = Eq[2].subs(n, n + 1)
    
    Eq.hypothesis = Eq[2].subs(x, x + 1)
    
    Eq <<= Eq[2] & Eq.hypothesis
        
    Eq << Eq[1].astype(Or)
    
    Eq <<= Eq[-1] & Eq[2]
    
    Eq.fx = Eq[-1].astype(Or).split()[0]
    
    Eq << Eq[1].subs(x, x + 1).astype(Or)
    
    Eq <<= Eq[-1] & Eq.hypothesis
    
    Eq << Eq[-1].astype(Or).split()[0]
    
    Eq <<= Eq[-1] & Eq.fx
    
    Eq << Eq.induction.induct()

        
if __name__ == '__main__':
    prove(__file__)
