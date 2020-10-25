from sympy.core.relational import Unequality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy.sets.contains import Subset
from sympy import Symbol

# given0: A != B 
# given1: A in B
# B - A != {}
@plausible
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
    return Unequality(B - A, S.EmptySet, given=given, evaluate=evaluate)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)
    inequality = Unequality(A, B)
    subset = Subset(A, B, evaluate=False) 
    
    Eq << apply(inequality, subset)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].union(A)
    
    Eq << Subset(B, A | B, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(subset).reversed
    
    Eq << Eq[-1].subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

