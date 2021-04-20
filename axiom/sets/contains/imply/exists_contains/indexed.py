from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given, index):
    x, S = axiom.is_Contains(given)   
    a = given.generate_free_symbol(**x.type.dict)
    return Exists[a:S](Equal(x[index], a[index]))


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True, shape=(n,))
    i = Symbol.i(integer=True)
    S = Symbol.S(etype=dtype.integer * n)
    
    Eq << apply(Contains(x, S), index=i)
    
    a = Eq[-1].variable
    
    Eq << algebra.exists.given.exists.subs.apply(Eq[-1], a, x)
    
    Eq << sets.exists_contains.given.is_nonemptyset.apply(Eq[-1])
    
    Eq << sets.contains.imply.is_nonemptyset.apply(Eq[0])
    
    
if __name__ == '__main__':
    prove()

