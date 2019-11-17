from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# provided0: A != B 
# provided1: A in B
# B - A != {}
def apply(*provided):
    assert len(provided) == 2
    A = None
    B = None    
    for p in provided:
        if p.is_Subset:
            A, B = p.args
        elif p.is_Unequality:
            _A, _B = p.args
        else:
            return
                         
    assert A == _A and B == _B or A == _B and B == _A
    return Unequality(B - A, S.EmptySet,
                    given=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)
    inequality = Unequality(A, B, evaluate = False)
    subset = Subset(A, B, evaluate = False) 
    
    Eq << inequality
    
    Eq << subset
    
    Eq << apply(inequality, subset)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].union(A)
    
    Eq << Subset(B, A, plausible = True)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq[-1].subs(subset)
    
    Eq << ~Eq[-1].reversed

    

if __name__ == '__main__':
    prove(__file__)

