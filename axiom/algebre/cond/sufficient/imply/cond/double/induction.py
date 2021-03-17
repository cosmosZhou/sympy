from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, n=None, x=None, start=0, hypothesis=False):
    start = sympify(start)
    f0, sufficient = given

    fn, fn1 = axiom.is_Sufficient(sufficient)
    
    x_wild = Wild('x', **x.type.dict)
    fn_hypothesis = fn
    fn = fn._subs(x, x_wild)
    
    x_, *_ = fn1._subs(n, n - 1).match(fn).values()
    
    x0_, *_ = f0.match(fn._subs(n, start)).values()

    assert n.domain.min() == start
    
    fn = fn._subs(x_wild, x_)
    if not hypothesis:
        return fn
    return fn, fn_hypothesis


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    
    Eq << apply(StrictGreaterThan(f[0](z), g[0](z)), Sufficient(StrictGreaterThan(f[n](x), g[n](x)), StrictGreaterThan(f[n + 1](y), g[n + 1](y))), n=n, x=x)
    
    Eq << Eq[0].subs(z, y)
    
    Eq << Eq[1].subs(x, y)
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq[-2], Eq[-1], n=n)

        
if __name__ == '__main__':
    prove(__file__)
