from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given, n=None, x=None, start=0, hypothesis=True):
    start = sympify(start)
    f0, sufficient = given
    axiom.is_Equal(f0)
    fn_and_fnt, fn1 = axiom.is_Sufficient(sufficient)
    
    fn, fnt = axiom.is_And(fn_and_fnt)
    
    if fn1._subs(n, n - 1) == fnt:
        fn, fnt = fnt, fn
        
    assert fn1._subs(n, n - 1) == fn
    
    x_wild = Wild('x', **x.type.dict)

    fn_ = fn._subs(x, x_wild)
    
    x_t, *_ = fnt.match(fn_).values()
    
    assert fn._subs(n, start) == f0

    assert n.domain.min() == start
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    t = Function.t(nargs=(), shape=(), real=True)
    x = Symbol.x(real=True)
    
    Eq << apply(Equal(f[0](x), g[0](x)), Sufficient(Equal(f[n](x), g[n](x)) & Equal(f[n](t(x)), g[n](t(x))), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)
    
    Eq << algebre.imply.sufficient.subs.apply(Eq[2], x, t(x))
    
    Eq << algebre.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq.induct = algebre.sufficient.sufficient.imply.sufficient.transit.apply(Eq[-1], Eq[1])
    
    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq[0], Eq.induct, n=n)
    
    
    
    
        
if __name__ == '__main__':
    prove(__file__)
