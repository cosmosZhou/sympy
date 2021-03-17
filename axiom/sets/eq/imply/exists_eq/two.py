from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(given, x=None, y=None):
    assert given.is_Equality
    abs_S, two = given.args
    assert abs_S.is_Abs
    assert two == 2
    S = abs_S.arg
     
    if x is None:
        x = S.generate_free_symbol(**S.etype.dict)
    if y is None:
        y = S.generate_free_symbol(excludes={x}, **S.etype.dict)
    return Exists[x: Unequality(x, y), y](Equality(S, {x, y}))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)
    Eq << apply(Equality(abs(S), 2))
    
    Eq << algebre.eq.imply.ge.apply(Eq[0])
    Eq << sets.ge.imply.exists_ne.apply(Eq[-1])
    
    Eq << sets.exists.imply.exists.limits_swap.apply(Eq[-1], simplify=False)
        
    Eq << algebre.exists_et.imply.exists.split.apply(Eq[-1], simplify=False)
    
    Eq.S_supset = Eq[-1] & Eq[-2]
    
    ab = Eq.S_supset.lhs
    
    Eq << Eq.S_supset.apply(sets.subset.imply.eq.union)
    
    Eq << sets.imply.eq.principle.addition.apply(S, ab)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Exists(Unequality(Eq[-1].lhs, 0), *Eq[-1].limits, plausible=True)
    
    Eq << Eq[-1].apply(algebre.is_nonzero.imply.eq.kronecker_delta)
    
    Eq << algebre.exists.imply.exists_et.multiple_variables.apply(Eq[-1])
    
    Eq << ~Eq[-2]
    
    Eq << Eq[-4].subs(Eq[-1])
    
    Eq << Eq[-1].apply(sets.is_zero.imply.subset)

    Eq <<= Eq[-1] & Eq.S_supset
    

if __name__ == '__main__':
    prove(__file__)

