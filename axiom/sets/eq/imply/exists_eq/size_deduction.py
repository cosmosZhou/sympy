from axiom.utility import prove, apply
from sympy import *
from axiom import sets, algebra
# given: |S| = 1
# Exists[x:S] ({x}) = S


@apply
def apply(given, var=None):
    assert given.is_Equal
    S_abs, n = given.args
    
    assert S_abs.is_Abs and n.is_extended_positive
    S = S_abs.arg
    if var is None:
        var = S.element_symbol()
    return Exists[var:S](Equal(abs(S - var.set), n - 1))




@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.integer)
    n = Symbol.n(integer=True, positive=True)

    Eq << apply(Equal(abs(S), n))
    
    Eq << algebra.eq.imply.ge.apply(Eq[0])
    
    Eq << sets.ge.imply.exists_contains.apply(Eq[-1], simplify=False)
    
    Eq << sets.exists_contains.imply.exists_contains.limits_restricted.apply(Eq[-1], simplify=False)
    
    i = Eq[-1].function.lhs     
    Eq << sets.imply.eq.principle.addition.apply(S, i.set)
    
    Eq << Eq[-2].this.function.apply(sets.contains.imply.eq.union)
    
    Eq << algebra.exists_eq.cond.imply.exists.subs.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].this.function - 1
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

