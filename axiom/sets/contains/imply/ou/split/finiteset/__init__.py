from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains
    e, finiteset = given.args
    finiteset = axiom.is_FiniteSet(finiteset, size=None)
    
    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    c = Symbol.c(integer=True, given=True)
    Eq << apply(Contains(e, {a, b, c}))
    
    u = Symbol.u(FiniteSet(a, b))
    Eq << u.this.definition
    
    Eq << (u | c.set).this.args[0].definition
    
    Eq << Eq[0].subs(Eq[-1].reversed)
    
    Eq << sets.contains.imply.ou.split.union.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].rhs.definition
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.ou.split.finiteset.two, simplify=None)
    

if __name__ == '__main__':
    prove()

from . import two
