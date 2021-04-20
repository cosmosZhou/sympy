from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


@apply(given=None)
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
    
    Eq << algebra.equivalent.given.cond.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.ou.split.finiteset.two, simplify=False)

    Eq << Eq[-1].this.rhs.apply(sets.ou.imply.contains.finiteset)

    
if __name__ == '__main__':
    prove()

