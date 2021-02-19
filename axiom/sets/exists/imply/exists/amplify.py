
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol
from sympy import Exists
from sympy.core.function import Function
from sympy.core.containers import Tuple


@apply
def apply(given, domain=None, wrt=None):
    assert given.is_Exists
    
    if wrt is None:
        i = 0
    else:
        i = given.variables.index(wrt)
        
    limits = [*given.limits]
    limit = limits[i]
    
    if domain is None:
        x = limit[0]
        limit = (x,)
    else:
        x, S = Tuple.as_setlimit(limit)
        assert S in domain
        limit = (x, domain)
        
    limits[i] = limit 
    return Exists(given.function, *limits)




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(Exists[e:S - {t}](f(e) > 0), domain=S)
    
    Eq << Eq[-1].bisect({t})
    
    Eq << Eq[-1].split()[0]


if __name__ == '__main__':
    prove(__file__)

