from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# provided: A in B 
# => {A} subset B
def apply(provided):
    assert provided.is_Contains
    e, s = provided.args
    
    return Subset(e.set, s,
                    given=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    e = Symbol('e', integer=True)
    s = Symbol('s', dtype=dtype.integer)
    contains = Contains(e, s, evaluate=False)
    
    Eq << contains
    
    Eq << apply(contains)
    
    Eq << Eq[-1].definition

if __name__ == '__main__':
    prove(__file__)

