from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
import axiom


@apply
def apply(self):
    x, expr, intersection = axiom.is_ImageSet(self)
    ss = axiom.is_Intersection(intersection)
    return Subset(self, Intersection(*(imageset(x, expr, s) for s in ss)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    
    x = Symbol.x(complex=True, shape=(n,))
    f = Function.f(complex=True, shape=(m,))    
    
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    
    Eq << apply(imageset(x, f(x), A & B))
    
    y = Symbol.y(complex=True, shape=(m,))
    
    S = Symbol.S(Eq[0].lhs)
    S_quote = Symbol("S'", Eq[0].rhs)
    
    Eq.sufficient = Sufficient(Contains(y, S), Contains(y, S_quote), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.apply(sets.contains.given.et.having.intersection, simplify=False)
    
    Eq << Eq[-1].apply(algebre.sufficient.given.et)
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq <<= Eq[-2].this.rhs.rhs.bisect(B), Eq[-1].this.rhs.rhs.bisect(A)
    
    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou, simplify=False), Eq[-1].this.rhs.apply(sets.contains.given.ou, simplify=False)

    Eq << sets.sufficient.imply.subset.apply(Eq.sufficient)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.rhs.definition
    
if __name__ == '__main__':
    prove(__file__)

