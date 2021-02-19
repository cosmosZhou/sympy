from sympy.core.relational import Unequality, Equality
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy import Exists, UNION, ForAll
from sympy import Symbol
from sympy.core.numbers import oo
from axiom import sets

@apply
def apply(given):
    assert given.is_Equality
    abs_S, n = given.args
    assert abs_S.is_Abs
    S = abs_S.arg
    i = S.generate_free_symbol(integer=True)
    j = S.generate_free_symbol(integer=True, excludes={i})
    kwargs = S.etype.dict
    if 'shape' in kwargs:        
        shape = (oo,) + kwargs['shape']
    else:
        shape = (oo,)
    kwargs.pop('shape', None)
    x = S.generate_free_symbol(shape=shape, **kwargs)
    return Exists[x[:n]:ForAll[j:i, i:n](Unequality(x[i], x[j]))](Equality(S, UNION[i:n]({x[i]})))




@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k, given=True)
    Eq << apply(Equality(abs(S), n))
    
    Eq << sets.imply.forall_exists_equal.general.apply(n, etype=S.etype, elements=Eq[-1].variable)
    
    Eq << Eq[-1].subs(Eq[-1].variable, S)
    
    Eq << Eq[-1].split()
    
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    prove(__file__)

