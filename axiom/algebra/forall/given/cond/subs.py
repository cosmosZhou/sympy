from axiom.utility import prove, apply
from sympy import *
import axiom
from sympy.concrete.limits import limits_dict
from axiom import algebra


@apply
def apply(given, old, new):
    cond, *limits = axiom.is_ForAll(given)
    
    domain_defined = new.domain
    domain = limits_dict(limits)[old]
    assert domain.is_set
    assert domain_defined in domain
    
    return cond._subs(old, new)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    m = Symbol.m(domain=Interval(0, n, integer=True))
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(ForAll[x:0:n + 1](Contains(f(x), s)), x, m)
    
    Eq << Eq[1].forall((m,))
    

if __name__ == '__main__':
    prove()

