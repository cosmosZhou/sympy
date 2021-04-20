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
        i = given.variables.index(wrt)
        
    limit = limits[i]
    
    assert domain is not None

    x, S = Tuple.as_setlimit(limit)
    assert S in domain 
    limit = (x, domain)
        
    limits[i] = limit
    return ForAll(function, *limits)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(ForAll[e:A](f(e) > 0), domain=A | B)    
    
    Eq << ~Eq[0]
    
    Eq << algebra.forall.exists.imply.exists_et.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    prove()

