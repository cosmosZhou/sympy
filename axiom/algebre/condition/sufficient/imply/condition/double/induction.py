from axiom.utility import prove, apply
from sympy.core.relational import Equal, StrictGreaterThan
from sympy import Symbol, Wild

from sympy.core.numbers import oo
from sympy import ForAll, Sufficient, LAMBDA, Or
import axiom
from axiom import algebre
from sympy.core.sympify import sympify
from sympy.core.function import Function


@apply(imply=True)
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
    
    Eq << algebre.sufficient.imply.forall.rewrite.apply(Eq[1], wrt=n)
    
#     Eq << algebre.equal.forall_equal.imply.equal.induction.apply(Eq[0], Eq[-1])

        
if __name__ == '__main__':
    prove(__file__)
