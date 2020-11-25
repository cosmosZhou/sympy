from sympy.core.relational import Unequality, Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.concrete.expr_with_limits import Exists, UNION, ForAll
from sympy import Symbol
from sympy.core.numbers import oo
from axiom import sets, algebre
# given: A != {}
# Exists[x] (x in A)


@plausible
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


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k)    
    Eq << apply(set=S)
    
    Eq << sets.imply.forall.apply(Eq[0], simplify=False)
    
    Eq << Eq[-1].apply(sets.equality.imply.exists_equality.two)


if __name__ == '__main__':
    prove(__file__)

