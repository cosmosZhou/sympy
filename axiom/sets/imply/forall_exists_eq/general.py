from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre

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
        
    return ForAll[S:Equality(abs(S), n)](Exists[x[:n]:ForAll[j:i, i:n](Unequality(x[i], x[j]))](Equality(S, UNION[i:n]({x[i]}))))




@prove
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)    
    Eq << apply(n, set=S)
    
    Eq.initial = Eq[0].subs(n, 2)
    
    Eq << Eq.initial.doit(deep=True)
    
    Eq << Eq[-1].this.function.limits[0][1].reversed
    
    Eq << sets.imply.forall_exists_eq.two.apply(*Eq[-1].rhs.args, set=Eq[-1].variable)
        
    Eq.induction = Eq[0].subs(n, n + 1)
    
    A = Eq.induction.function.variable.base
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.induction.limits)
    
    Eq.size_deduction = Eq[-1].apply(sets.eq.imply.exists_eq.size_deduction, var=A[n])
    
    Eq << Eq[0].subs(Eq.size_deduction.variable, Eq.size_deduction.lhs.arg)
    
    Eq << Eq[-1].subs(Eq.size_deduction)
    
    Eq.S_union_An, Eq.nonoverlapping = Eq[-1].apply(sets.eq.imply.eq.union, A[n].set), \
        Eq[-1].apply(sets.eq.imply.eq.intersect, A[n].set).reversed
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq.size_deduction.function.limits)
    
    Eq << Eq[-1].apply(sets.contains.imply.eq.union)
    
    Eq << Eq.S_union_An.subs(Eq[-1])
    
    Eq << Eq.nonoverlapping.apply(sets.is_emptyset.imply.notcontains, simplify=None)
    
    Eq << Eq[-1].apply(sets.notcontains.imply.forall_notcontains)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.amplify, wrt=A[n], depth=1)
    
    Eq << Eq[-1].apply(algebre.exists_et.imply.exists.limits_absorb, index=1, depth=1)
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.limits_swap, depth=1)
    
    Eq << algebre.forall_exists_forall_et.imply.forall.apply(Eq[-1])
    
    Eq << Eq[-1].apply(sets.forall_ne.forall_ne.imply.forall_ne, Eq[-2], depth=2)
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.limits_swap, depth=1)
    
    Eq << Eq.induction.induct()
    
    Eq << algebre.cond.sufficient.imply.cond.induction.apply(Eq.initial, Eq[-1], start=2, n=n)

if __name__ == '__main__':
    prove(__file__)

