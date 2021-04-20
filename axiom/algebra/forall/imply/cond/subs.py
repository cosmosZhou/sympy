from axiom.utility import prove, apply
from sympy import *
import axiom
from sympy.concrete.limits import limits_dict
from axiom import algebra


@apply
def apply(given, old, new):
    cond, *limits = axiom.is_ForAll(given)
    
    domain = limits_dict(limits)[old]
    if domain.is_set:
        assert new in domain
    elif domain.is_boolean:
        assert domain._subs(old, new)
    else:
        return
    
    return cond._subs(old, new)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(ForAll[x:0:n + 1](Contains(f(x), s)), x, n)
    
    Eq << algebra.forall.imply.et.split.apply(Eq[0], cond={n})
    
    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)
    

if __name__ == '__main__':
    prove()

