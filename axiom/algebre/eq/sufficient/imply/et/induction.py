from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
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


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    x = Symbol.x(real=True)
    
    Eq << apply(Equal(f[0](x), g[0](x)), Sufficient(Equal(f[n](x), g[n](x)) & Equal(f[n](x + 1), g[n](x + 1)), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)
    
    fn = Eq[2].args[1]
    Eq << Sufficient(fn, fn._subs(x, x + 1), plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(algebre.eq.imply.eq.subs, x, x + 1)
    
    Eq << algebre.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << algebre.sufficient.sufficient.imply.sufficient.transit.apply(Eq[-1], Eq[1])
    
    Eq << algebre.eq.sufficient.imply.eq.induction.apply(Eq[0], Eq[-1], n=n)    
    
    Eq << Eq[-1].subs(x, x + 1)
    
    Eq <<= Eq[-1] & Eq[-2]

    
if __name__ == '__main__':
    prove(__file__)
