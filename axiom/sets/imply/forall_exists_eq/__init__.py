from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(n, **kwargs):
    if 'etype' in kwargs:
        etype = kwargs['etype']
        if 'elements' in kwargs:
            S = n.generate_free_symbol(etype=etype, excludes=kwargs['elements'].free_symbols)
        else:
            S = n.generate_free_symbol(etype=etype)
    else:
        S = kwargs['set']
        etype = S.etype
        
    i = n.generate_free_symbol(integer=True)
    j = S.generate_free_symbol(integer=True, excludes={i})
    
    if 'elements' in kwargs:
        x = kwargs['elements']
    else:
        kwargs = etype.dict
        if 'shape' in kwargs: 
            shape = (oo,) + kwargs['shape']
        else:
            shape = (oo,)
        kwargs.pop('shape')

        x = S.generate_free_symbol(shape=shape, **kwargs)
        
    return ForAll[S:Equal(abs(S), n)](Exists[x[:n]:ForAll[j:i, i:n](Unequal(x[i], x[j]))](Equal(S, UNION[i:n]({x[i]}))))


@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True), given=False)
    
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)    
    Eq << apply(n, set=S)
    
    Eq.initial = Eq[0].subs(n, 2)
    
    Eq << Eq.initial.this.function.doit(deep=True)
        
    Eq << Eq[-1].this.function.limits[0][1].reversed
    
    Eq << sets.imply.forall_exists_eq.two.apply(*Eq[-1].rhs.args, set=Eq[-1].variable)
        
    Eq.induction = Eq[0].subs(n, n + 1)
    
    A = Eq.induction.function.variable.base
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq.induction.limits)
    
    Eq.size_deduction = Eq[-1].this.function.apply(sets.eq.imply.exists_eq.size_deduction, var=A[n])
    
    Eq << algebra.forall.imply.ou.subs.apply(Eq[0], Eq.size_deduction.variable, Eq.size_deduction.lhs.arg)
    
    Eq << algebra.ou.imply.exists_ou.apply(Eq[-1])
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq[-1], Eq.size_deduction)
    
    Eq << Eq[-1].this.function.apply(algebra.exists.exists.imply.exists_et)
    
    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.cond, index=0)
    
    Eq << Eq[-1].this.function.function.apply(sets.eq.imply.eq.union_intersect, A[n].set)
    
    Eq << algebra.imply.forall.limits_assert.apply(Eq.size_deduction.function.limits)
    
    Eq << Eq[-1].this.function.apply(sets.contains.imply.eq.union)
    
    Eq << algebra.cond.forall.imply.forall_et.apply(Eq[-1], Eq[-3])
    
    Eq << Eq[-1].this.function.apply(algebra.forall.exists.imply.exists_et)
    
    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.et.subs)
    
    Eq << Eq[-1].this.function.function.apply(algebra.et.imply.et.delete, index=1)
    
    Eq << Eq[-1].this.find(Equal[2]).apply(sets.is_emptyset.imply.notcontains, simplify=None)
    
    Eq << Eq[-1].this.find(NotContains).apply(sets.notcontains.imply.forall_notcontains)
    
    Eq << Eq[-1].this.function.apply(sets.exists.imply.exists.limits.relax, wrt=A[n])
    
    Eq << Eq[-1].this.function.apply(algebra.exists_et.imply.exists.limits_absorb, index=1)
    
    Eq << Eq[-1].this.function.apply(sets.exists.imply.exists.limits.swap)
    
    Eq << Eq[-1].this.function.function.apply(sets.forall_ne.forall_ne.imply.forall_ne)
    
    Eq << Eq[-1].this.function.apply(sets.exists.imply.exists.limits.swap)
    
    Eq << Eq.induction.induct()
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], start=2, n=n)


if __name__ == '__main__':
    prove()

from . import two
from . import split
