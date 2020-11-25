from sympy.core.relational import Unequality, Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.concrete.expr_with_limits import Exists, UNION, ForAll
from sympy import Symbol
from sympy.core.numbers import oo
from axiom import sets
from sympy.sets.sets import Interval
# given: A != {}
# Exists[x] (x in A)


@plausible
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


from axiom.utility import check


@check
def prove(Eq):
#     n = Symbol.n(integer=True, positive=True)
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)    
    Eq << apply(n, set=S)
    
    Eq << Eq[0].subs(n, 2)
    
    Eq << Eq[-1].doit(deep=True)
    
    Eq << Eq[-1].this.function.limits[0][1].reversed
    
    Eq << sets.imply.forall_exists_equality.two.apply(*Eq[-1].rhs.args, set=Eq[-1].variable)
        
    Eq << Eq[0].subs(n, n + 1)
    
    A = Eq[-1].function.variable.base
    
    Eq << sets.imply.forall.apply(Eq[-1], simplify=False)
    Eq.size_deduction = Eq[-1].apply(sets.equality.imply.exists_equality.size_deduction, var=A[n])
    
    Eq << Eq[0].subs(Eq.size_deduction.variable, Eq.size_deduction.lhs.arg)
    
    Eq << Eq[-1].subs(Eq.size_deduction)
    
    Eq.S_union_An, Eq.nonoverlapping = Eq[-1].union(A[n].set), Eq[-1].intersect(A[n].set).reversed
    
    Eq << Eq.size_deduction.apply(sets.imply.forall, depth=1, simplify=None)
    
    Eq << Eq[-1].apply(sets.contains.imply.equality.union)
    
    Eq << Eq.S_union_An.subs(Eq[-1])
    
    Eq << Eq.nonoverlapping.apply(sets.is_emptyset.imply.notcontains)
    
    Eq << Eq[-1].apply(sets.notcontains.imply.forall_notcontains)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.enlargement, wrt=A[n], depth=1)
    
    Eq << Eq[-1].apply(sets.exists_et.imply.exists.limits_absorb, index=1, depth=1)
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.limits_swap, depth=1)
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-1].apply(sets.forall_inequality.forall_inequality.imply.forall_inequality, Eq[-2], depth=2)
    
    Eq << Eq[-1].apply(sets.exists.imply.exists.limits_swap, depth=1)

if __name__ == '__main__':
    prove(__file__)

