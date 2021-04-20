from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given):
    assert given.is_Exists
    limit, *limits = given.limits
    assert len(limit) == 1
    x = limit[0]
    assert given.function.is_Contains
    _x, S = given.function.args
    assert x == _x
    return Exists(Contains(x, S), (x, S), *limits)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real, given=True)
    e = Symbol.e(real=True)
    t = Symbol.t(real=True)

    Eq << apply(Exists[e, t:S](Contains(e, S - {t})))
    
    Eq << Eq[-1].simplify()
    
    Eq << ~Eq[-1]    
    
    Eq << sets.exists_contains.imply.is_nonemptyset.apply(Eq[0], simplify=None)
    
    Eq << algebra.cond.imply.forall.restrict.apply(Eq[-1], (t, S))
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << algebra.eq.ne.imply.ne.subs.apply(Eq[-1], Eq[-3])   


if __name__ == '__main__':
    prove()

