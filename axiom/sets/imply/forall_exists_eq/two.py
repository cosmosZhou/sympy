
from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebre
# given: A != {}
# Exists[x] (x in A)


@apply
def apply(x=None, y=None, **kwargs):
    if 'etype' in kwargs:
        etype = kwargs['etype']
        S = Symbol.S(etype=etype)
    else:
        S = kwargs['set']
        
    if x is None:
        x = S.generate_free_symbol(**S.etype.dict)
    if y is None:
        y = S.generate_free_symbol(excludes={x}, **S.etype.dict)

    return ForAll[S:Equality(abs(S), 2)](Exists[x: Unequality(x, y), y](Equality(S, {x, y})))




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)    
    Eq << apply(set=S)
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq[0].limits)
    
    Eq << Eq[-1].apply(sets.eq.imply.exists_eq.two)


if __name__ == '__main__':
    prove(__file__)

