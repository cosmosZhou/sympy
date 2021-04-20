from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, domain=None, wrt=None):
    function, *limits = axiom.is_ForAll(given)
    
    if isinstance(domain, tuple):
        wrt, *domain = domain
        if len(domain) == 1:
            domain = domain[0]
            
    if wrt is None:
        i = 0
    else:
        try:
            i = given.variables.index(wrt)
        except ValueError:
            limits.append((wrt,))
            i = -1
        
    limit = limits[i]
    
    if len(limit) == 1:
        x = limit[0]
        S = x.universalSet
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
    f = Function.f(shape=(), integer=True)

    Eq << apply(ForAll[e:S](f(e) > 0), domain=S // {t})
    
    Eq << algebra.forall.imply.et.split.apply(Eq[0], cond={t})
    
    Eq << algebra.et.imply.cond.apply(Eq[-1], 0)


if __name__ == '__main__':
    prove()

