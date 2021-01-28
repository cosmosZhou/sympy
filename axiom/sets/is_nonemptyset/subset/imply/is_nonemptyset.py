from axiom.utility import prove, apply

from sympy import *
from axiom import sets


# given0: A != B 
# given1: A in B
# B - A != {}
@apply(imply=True)
def apply(*given, evaluate=False):
    assert len(given) == 2
    A = None
    B = None    
    for p in given:
        if p.is_Subset:
            A, B = p.args
        elif p.is_Unequality:
            _A, _B = p.args
        else:
            return
                         
    assert A == _A and B == _B or A == _B and B == _A
    return Unequality(B - A, A.etype.emptySet, evaluate=evaluate)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    inequality = Unequality(A, B)
    subset = Subset(A, B, evaluate=False) 
    
    Eq << apply(inequality, subset)
    
    Eq << ~Eq[-1]
    
    Eq << sets.equal.imply.equal.union.apply(Eq[-1], A)
    
    Eq << Subset(B, A | B, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(subset).reversed
    
    Eq << Eq[-1].subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

