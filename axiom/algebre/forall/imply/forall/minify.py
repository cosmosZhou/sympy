from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = axiom.is_ForAll(given)
    
    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)
        
    limit = limits[i]
    
    if domain is None:
        x = limit[0]
        limit = (x,)
    else:
        x, S = Tuple.as_setlimit(limit)
        assert domain in S 
        limit = (x, domain)
        
    limits[i] = limit 
    return ForAll(function, *limits)




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(ForAll[e:S](f(e) > 0), domain=S - {t})
    
    Eq << Eq[0].bisect({t})
    
    Eq << algebre.et.imply.cond.apply(Eq[-1], 0)


if __name__ == '__main__':
    prove(__file__)

