from sympy.core.relational import Unequality, Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.concrete.expr_with_limits import Exists
from sympy import Symbol
from axiom import sets, algebre


@plausible
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
    return Exists[x: Unequality(x, y), y](Equality(S, {x, y}), given=given)


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)
    Eq << apply(Equality(abs(S), 2))
    
    Eq << algebre.equality.imply.greater_than.apply(Eq[0])
    Eq << sets.greater_than.imply.exists_inequality.apply(Eq[-1])
    
    Eq << sets.exists.imply.exists.limits_swap.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].split(simplify=False)
    
    Eq.S_supset = Eq[-1] & Eq[-2]
    
    ab = Eq.S_supset.lhs
    
    Eq << Eq.S_supset.apply(sets.subset.imply.equality.union)
    
    Eq << sets.imply.equality.principle.addition.apply(S, ab)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Exists(Unequality(Eq[-1].lhs, 0), *Eq[-1].limits, plausible=True)
    
    Eq << Eq[-1].apply(algebre.is_nonzero.imply.equality.kronecker_delta)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].apply(sets.is_zero.imply.subset)

    Eq <<= Eq[-1] & Eq.S_supset
    

if __name__ == '__main__':
    prove(__file__)

