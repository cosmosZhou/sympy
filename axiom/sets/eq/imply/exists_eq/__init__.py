from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given):
    assert given.is_Equal
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
    return Exists[x[:n]:ForAll[j:i, i:n](Unequal(x[i], x[j]))](Equal(S, UNION[i:n]({x[i]})))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    S = Symbol.S(etype=dtype.integer * k, given=True)
    Eq << apply(Equal(abs(S), n))
    
    Eq << sets.imply.forall_exists_eq.apply(n, etype=S.etype, elements=Eq[-1].variable)
    
    Eq.ou = algebra.forall.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, S)
    
    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq.ou)


if __name__ == '__main__':
    prove()

from . import size_deduction
from . import two
from . import one
