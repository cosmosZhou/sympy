from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebre


@apply
def apply(given, f):
    x, s = axiom.is_Contains(given)
    if x.is_given:
        z = s.generate_free_symbol(**x.type.dict)
        S = imageset(z, f(z), s)
    else:
        S = imageset(x, f(x), s)
    return Contains(f(x), S)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(y, s), f=f)
    
    S = Symbol.S(Eq[1].rhs)
    
    Eq << S.this.definition
    
    Eq << Eq[1].subs(Eq[-1].reversed)
    
    Eq.forall_contains = ForAll[x:s](Contains(f(x), S), plausible=True)
    
    Eq << Eq.forall_contains.this.function.rhs.definition
    
    Eq << Eq[-1].this.function.apply(sets.contains.given.subset, simplify=False)
    
    Eq << sets.forall_subset.given.subset.lhs.apply(Eq[-1])
        
    Eq << Eq.forall_contains.subs(x, y)
    
    Eq << algebre.cond.ou.imply.cond.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

