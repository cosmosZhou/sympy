from sympy.core.symbol import Symbol
from sympy.utility import plausible, identity
from sympy.core.relational import Equality
from sympy.sets.sets import Interval


@plausible
def apply(x, y):
    return Equality(x @ y, y @ x)


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    x = Symbol('x', shape=(n,), real=True)
    y = Symbol('y', shape=(n,), real=True)
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    Eq << apply(x, y)
    
    Eq << identity(Eq[0].lhs).expand(free_symbol=i)
    
    Eq << identity(Eq[0].rhs).expand(free_symbol=i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
        

if __name__ == '__main__':
    prove(__file__)
