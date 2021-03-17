from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, reverse=False):
    exists_equal, cond = given
    fn, *limits = axiom.exists_equal(exists_equal)   
    
    x, y = fn.args
    if reverse:
        x, y = y, x
    return Exists(cond._subs(x, y), *limits)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Exists[x:S](Equal(g(x), f(x))), g(x) > y)
    
    Eq <<= Eq[0] & Eq[1]
    
    Eq << Eq[-1].this.function.apply(algebre.eq.cond.imply.cond.subs)

    
if __name__ == '__main__':
    prove(__file__)

