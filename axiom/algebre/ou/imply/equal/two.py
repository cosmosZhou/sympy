from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom.sets.ou.imply.contains.two import expr_cond_pair
from axiom import sets, algebre


@apply(imply=True)
def apply(given, wrt=None):
    or_eqs = axiom.is_Or(given)
    assert len(or_eqs) == 2
    return Equality(wrt, Piecewise(*expr_cond_pair(Equality, or_eqs, wrt, reverse=True)).simplify())


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    f = Function.f(nargs=(k,), shape=(k,), real=True)
    g = Function.g(nargs=(k,), shape=(k,), real=True)
    h = Function.h(nargs=(k,), shape=(k,), real=True)
    
    p = Symbol.p(real=True, shape=(k,), given=True)
    
    Eq << apply(Equality(p, f(x)) & Contains(x, A) | Equality(g(x), p) & NotContains(x, A), wrt=p)
    
    Eq << Eq[1].bisect(Contains(x, A)).split()
    
    Eq <<= ~Eq[-2], ~Eq[-1]

    Eq <<= Eq[-2].apply(algebre.condition.condition.imply.et, invert=True, swap=True), Eq[-1].apply(algebre.condition.condition.imply.et, swap=True)
    
    Eq <<= Eq[-2] & Eq[0], Eq[-1] & Eq[0]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-2].astype(Or)


if __name__ == '__main__':
    prove(__file__)

