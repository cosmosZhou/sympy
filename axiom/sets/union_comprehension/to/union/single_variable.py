from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom

@apply
def apply(self):
    fx, *limits = axiom.is_UNION(self)
    return Equal(self, fx.as_multiple_terms(*axiom.limit_is_set(limits), cls=UNION))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
     
    Eq << apply(UNION[x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))
    
    Eq << sets.eq.given.sufficient.apply(Eq[0], wrt='y')
    
    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.exists_contains.st.union_comprehension),\
    Eq[-1].this.rhs.apply(sets.contains.given.exists_contains.st.union_comprehension)
    
    Eq <<= Eq[-2].this.lhs.function.apply(sets.contains.imply.ou.st.piecewise),\
    Eq[-1].this.rhs.function.apply(sets.contains.given.ou.st.piecewise)
    
    Eq <<= Eq[-2].this.lhs.apply(algebra.exists_ou.imply.ou.exists),\
    Eq[-1].this.rhs.apply(algebra.exists_ou.given.ou.exists)
    
    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.exists_et.imply.exists.limits_absorb, index=0),\
    Eq[-1].this.rhs.args[0].apply(algebra.exists_et.given.exists.limits_absorb, index=0)
    
    Eq <<= Eq[-2].this.lhs.args[1].apply(algebra.exists_et.imply.exists.limits_absorb, index=0),\
    Eq[-1].this.rhs.args[1].apply(algebra.exists_et.given.exists.limits_absorb, index=0)
    
    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.ou.split.union, simplify=None),\
    Eq[-1].this.lhs.apply(sets.contains.imply.ou.split.union, simplify=None)
    
    Eq <<= Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.exists_contains.st.union_comprehension),\
    Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.exists_contains.st.union_comprehension)
    
    Eq << Eq[-2].this.rhs.find(Contains).apply(sets.contains.given.exists_contains.st.union_comprehension)

    Eq << Eq[-1].this.lhs.find(Contains).apply(sets.contains.imply.exists_contains.st.union_comprehension)

if __name__ == '__main__':
    prove()

