from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets, algebre
from sympy.sets.sets import imageset, image_set


@apply(imply=True)
def apply(given, f):
    x, s = axiom.is_Contains(given)
    S = image_set(f(x), x, s)
    return Contains(f(x), S)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(y, s), f=f)
    
    S = Symbol.S(definition=Eq[1].rhs)
    
    Eq << S.this.definition
    
    Eq << Eq[1].subs(Eq[-1].reversed)
    
    Eq.forall_contains = ForAll[x:s](Contains(f(x), S), plausible=True)
    
    Eq << Eq.forall_contains.this.function.rhs.definition
    
    Eq << Eq[-1].this.function.apply(sets.contains.given.exists_equal.where.imageset)
    
    i = Eq[-1].function.variable
    Eq << Eq[-1].this.function.apply(algebre.exists.given.exists.subs, i, x, depth=0)
    
    Eq << sets.contains.imply.is_nonemptyset.apply(Eq[0])
    
    Eq << Eq.forall_contains.subs(x, y)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Eq[-1].split()
    
if __name__ == '__main__':
    prove(__file__)

