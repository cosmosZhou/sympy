from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply(imply=True, given=None)
def apply(given):
    x, finiteset = axiom.is_Contains(given)
    finiteset = axiom.is_FiniteSet(finiteset, size=None)
    
    return Equivalent(given, Or(*(Equal(x, e) for e in finiteset)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(Contains(x, {a, b}))
    
    Eq << Sufficient(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.ou.where.finiteset.two, simplify=False)

    Eq << Necessary(*Eq[0].args, plausible=True)
    
    Eq << Eq[-1].this.rhs.apply(sets.ou.imply.contains.finiteset)

    Eq <<= Eq[2] & Eq[1]

    
if __name__ == '__main__':
    prove(__file__)

