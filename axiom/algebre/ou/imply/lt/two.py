from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets, algebre


@apply
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    assert len(or_eqs) == 2
    return StrictLessThan(Piecewise(*expr_cond_pair(StrictLessThan, or_eqs, wrt, reverse=True)).simplify(), wrt)


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(StrictLessThan(f(x), p) & Contains(x, A) | StrictLessThan(g(x), p) & NotContains(x, A), wrt=p)
    
    Eq << Eq[1].bisect(Contains(x, A))
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebre.cond.cond.imply.et, invert=True, swap=True), Eq[-1].apply(algebre.cond.cond.imply.et, swap=True)
    
    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-2].astype(Or)


if __name__ == '__main__':
    prove(__file__)

