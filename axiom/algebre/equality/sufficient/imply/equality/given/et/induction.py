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


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    t = Function.t(nargs=(), shape=(), real=True)
    x = Symbol.x(real=True)
    
    Eq << apply(Equal(f[0](x), g[0](x)), Sufficient(Equal(f[n](x), g[n](x)) & Equal(f[n](t(x)), g[n](t(x))), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)
    
    Eq << algebre.sufficient.imply.forall.rewrite.apply(Eq[1], wrt=n)
    
    Eq << Eq[0].subs(x, t(x))
    
    Eq <<= Eq[-1] & Eq[0]
    
#     h = Symbol.h(definition=LAMBDA[n](Eq[1].lhs))

    Eq.imply_induct = Sufficient(Eq[1].lhs, Eq[1].lhs._subs(n, n + 1), plausible=True)
    
    Eq << Eq.imply_induct.split()
    
    Eq << Eq[1].subs(x, t(x))
    
    Eq << Sufficient(Eq.imply_induct.lhs, Eq[-1].lhs)
#     Eq << Sufficient(Eq.imply_induct.lhs, Eq[-1].lhs, plausible=True)
    
    Eq << algebre.sufficient.sufficient.imply.sufficient.transit.apply(Eq[-1], Eq[-2])
    
#     Eq << algebre.equality.forall_equality.imply.equality.induction.apply(Eq[0], Eq[-1])

        
if __name__ == '__main__':
    prove(__file__)
